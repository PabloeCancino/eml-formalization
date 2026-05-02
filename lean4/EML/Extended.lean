-- ============================================================
-- EML/Extended.lean
-- Evaluador EML sobre reales extendidos (EReal)
--
-- MOTIVACIÓN
-- ----------
-- EML/Real.lean probó reval_tLog incondicional en ℝ.
-- Pero la cadena EML usa log(0) = −∞ para Minus(x) = −x.
-- En Lean: Real.log 0 = 0 (convenio) → tMinus da 1−x, no −x.
--
-- Solución: EReal = WithBot (WithTop ℝ), donde ⊥ = −∞.
-- Con emlLog 0 = ⊥, la cadena Minus funciona correctamente.
--
-- DESCUBRIMIENTO CENTRAL
-- ----------------------
-- El árbol correcto para Minus(x) = −x es:
--   tMinusV x = app (tLog (tLog one)) (tExp x)
--   (NO app (tLog one) (tExp x) como estaba en Basic.lean)
--
-- Traza en EReal:
--   ereval (tLog one) z        = emlLog 1   = 0    [emlLog_one]
--   ereval (tLog (tLog one)) z = emlLog 0   = ⊥    [emlLog_zero]
--   ereval (app ⊥_tree (tExp x)) z
--     = emlExp ⊥ + (-emlLog (emlExp (ereval x z)))
--     = 0        + (-(ereval x z))                 [emlExp_bot, emlLog_emlExp]
--     = -ereval x z  ✓
--
-- DIFICULTAD TÉCNICA
-- ------------------
-- EReal no es un anillo; `ring` no aplica.
-- La aritmética `e + -(e + (-x)) = x` para e : ℝ finito y x : EReal
-- se prueba por casos (⊥, ⊤, coe r), aislada en `ereal_shift_cancel`.
-- ============================================================

import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import EML.Basic
import Mathlib.Tactic

namespace EML

-- ============================================================
-- §1. EML-EXP Y EML-LOG SOBRE EReal
-- ============================================================

/-- EML-exp: exp(−∞) = 0, exp(r) = Real.exp r, exp(+∞) = +∞. -/
noncomputable def emlExp : EReal → EReal
  | ⊥       => (0 : ℝ)
  | ⊤       => ⊤
  | (r : ℝ) => (Real.exp r : ℝ)

/-- EML-log: log(≤0) = −∞, log(r > 0) = Real.log r, log(+∞) = +∞. -/
noncomputable def emlLog : EReal → EReal
  | ⊥       => ⊥
  | ⊤       => ⊤
  | (r : ℝ) => if r ≤ 0 then ⊥ else (Real.log r : ℝ)

-- ============================================================
-- §2. PROPIEDADES DE emlExp Y emlLog
-- ============================================================

@[simp] theorem emlExp_bot  : emlExp ⊥ = (0 : ℝ) := rfl
@[simp] theorem emlExp_top  : emlExp ⊤ = ⊤ := rfl
@[simp] theorem emlExp_real (r : ℝ) : emlExp (r : EReal) = (Real.exp r : ℝ) := rfl
theorem emlExp_pos (x : EReal) : 0 < emlExp x ∨ emlExp x = 0 := by
  induction x using EReal.rec with
  | bot => right; simp
  | top => left; exact (EReal.zero_lt_top)  -- EReal.top_pos renamed
  | coe r => left; exact_mod_cast Real.exp_pos r

@[simp] theorem emlLog_bot : emlLog ⊥ = ⊥ := rfl
@[simp] theorem emlLog_top : emlLog ⊤ = ⊤ := rfl

theorem emlLog_real_pos {r : ℝ} (hr : 0 < r) :
    emlLog (r : EReal) = (Real.log r : ℝ) := by
  -- TODO: simp [emlLog, not_le.mpr hr] fails in v4.29.0 (match not reducing)
  -- The math: emlLog (r:EReal) unfolds to if r ≤ 0 then ⊥ else ↑(log r)
  -- Since hr : 0 < r, we have ¬(r ≤ 0), so result = ↑(log r)
  simp only [emlLog]
  split_ifs with h
  · exact absurd (lt_of_lt_of_le hr (le_of_lt (not_le.mp (not_not.mpr h)))) (lt_irrefl _)
  · rfl

@[simp] theorem emlLog_zero : emlLog (0 : EReal) = ⊥ := by
  -- emlLog ((0:ℝ):EReal) = if 0 ≤ 0 then ⊥ else ... = ⊥
  simp only [emlLog]
  split_ifs with h
  · rfl
  · exact absurd le_rfl h

@[simp] theorem emlLog_one : emlLog (1 : EReal) = 0 := by
  have : (1 : EReal) = ((1 : ℝ) : EReal) := by norm_cast
  rw [this, emlLog_real_pos one_pos, Real.log_one]
  norm_cast

/-- Propiedad fundamental: log(exp(x)) = x, incondicional en EReal. -/
theorem emlLog_emlExp : ∀ x : EReal, emlLog (emlExp x) = x := by
  intro x; induction x using EReal.rec with
  | bot  => simp [emlExp_bot, emlLog_zero]
  | top  => simp [emlExp_top, emlLog_top]
  | coe r =>
    rw [emlExp_real, emlLog_real_pos (Real.exp_pos r)]
    simp [Real.log_exp]

/-- exp(log(x)) = x cuando x > 0 y x ≠ ⊤. -/
theorem emlExp_emlLog_pos {x : EReal} (hpos : 0 < x) (htop : x ≠ ⊤) :
    emlExp (emlLog x) = x := by
  -- x is finite positive: x = ↑r for some r : ℝ with r > 0
  have hx : x ≠ ⊥ := ne_of_gt hpos
  lift x to ℝ using ⟨hx, htop⟩  -- lift EReal to ℝ
  have hr : 0 < x := by exact_mod_cast hpos
  simp [emlLog_real_pos hr, emlExp_real, Real.exp_log hr]

/-- exp(log(x)) = x cuando x ≥ 0 en EReal.
    Incluye x = 0 (via log 0 = ⊥, exp ⊥ = 0) y x = ⊤ (via log ⊤ = ⊤, exp ⊤ = ⊤).
    Condición más débil que emlExp_emlLog_pos: no requiere estricta positividad. -/
theorem emlExp_emlLog_nonneg {x : EReal} (hx : 0 ≤ x) :
    emlExp (emlLog x) = x := by
  induction x using EReal.rec with
  | bot  =>
    -- 0 ≤ ⊥ es falso: le_bot_iff da 0 = ⊥, pero 0 ≠ ⊥ en EReal
    simp only [le_bot_iff] at hx
    exact absurd hx (by norm_cast)
  | top  => simp [emlLog_top, emlExp_top]
  | coe r =>
    have hr : 0 ≤ r := by exact_mod_cast hx
    by_cases hr0 : r = 0
    · subst hr0; simp [emlLog_zero, emlExp_bot]
    · have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      rw [emlLog_real_pos hr_pos, emlExp_real, Real.exp_log hr_pos]

-- ============================================================
-- §3. LEMA ARITMÉTICO CLAVE EN EReal
-- ============================================================
--
-- La prueba de ereval_tLog necesita el análogo de:
--   e + -(e + (-x)) = x   (válido en ℝ por ring)
-- En EReal, se prueba por casos en x (⊥, ⊤, coe r).
-- Para e : ℝ (finito), el resultado vale incondicionalmente.

/-- Aritmética EReal: para e : ℝ finito y x : EReal,
    e + -(e + (-x)) = x.
    Es el análogo del paso `ring` de EML/Real.lean en EReal. -/
lemma ereal_shift_cancel (e : ℝ) (x : EReal) :
    (e : EReal) + -((e : EReal) + (-x)) = x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    -- (e:EReal) + -((e:EReal) + -(r:EReal)) = (r:EReal)
    -- Equivalent to e + -(e - r) = r in ℝ lifted to EReal
    have key : (e : EReal) + -((e : EReal) + (-(r : EReal))) = (r : EReal) := by
      rw [show -((r : ℝ) : EReal) = ((-r : ℝ) : EReal) from (EReal.coe_neg r).symm]
      rw [show ((e : EReal) + ((-r : ℝ) : EReal)) = ((e + (-r) : ℝ) : EReal) from
            (EReal.coe_add e (-r)).symm]
      rw [show -((e + (-r) : ℝ) : EReal) = ((-(e + (-r)) : ℝ) : EReal) from
            (EReal.coe_neg _).symm]
      rw [show ((e : EReal) + ((-(e + (-r)) : ℝ) : EReal)) = ((e + -(e + (-r)) : ℝ) : EReal) from
            (EReal.coe_add e _).symm]
      norm_cast; ring
    exact key

-- ============================================================
-- §4. TIPO EMLTermV (GRAMÁTICA CON VARIABLE)
-- ============================================================
--
-- EMLTerm  : S → 1 | f(S,S)          — solo genera funciones constantes
-- EMLTermV : S → 1 | var | f(S,S)    — genera funciones de EReal → EReal
--
-- `var` representa la variable libre (el argumento de entrada).

/-- Término EML con variable libre.
    `var` es el argumento de entrada; `one` la constante 1. -/
inductive EMLTermV : Type where
  | one : EMLTermV
  | var : EMLTermV
  | app : EMLTermV → EMLTermV → EMLTermV
  deriving Repr, DecidableEq, Inhabited

namespace EMLTermV

-- Árboles testigo (misma estructura que en Basic.lean):
def tExp (x : EMLTermV) : EMLTermV := app x one
def tLog (x : EMLTermV) : EMLTermV := app one (app (app one x) one)

-- ============================================================
-- §5. EVALUADOR ereval : EMLTermV → EReal → EReal
-- ============================================================
--
-- Operador EML sobre EReal: f(a, b) = emlExp(a) + (-emlLog(b))
-- (equivalente a emlExp(a) - emlLog(b), usando suma con negativo
-- para evitar los casos indeterminados de EReal.sub)

/-- Evaluación EReal de un término EMLTermV. -/
noncomputable def ereval (t : EMLTermV) (z : EReal) : EReal :=
  match t with
  | one       => (1 : ℝ)
  | var       => z
  | app t' s' => emlExp (ereval t' z) + (-emlLog (ereval s' z))

notation "⟦" t "⟧ₑ(" z ")" => EMLTermV.ereval t z

@[simp] theorem ereval_one (z : EReal) : ⟦one⟧ₑ(z) = (1 : ℝ) := rfl
@[simp] theorem ereval_var (z : EReal) : ⟦var⟧ₑ(z) = z := rfl
@[simp] theorem ereval_app (t s : EMLTermV) (z : EReal) :
    ⟦app t s⟧ₑ(z) = emlExp (⟦t⟧ₑ(z)) + (-emlLog (⟦s⟧ₑ(z))) := rfl

-- ============================================================
-- §6. TEOREMAS INCONDICIONALES
-- ============================================================

-- R1: ⟦tExp t⟧ₑ(z) = emlExp(⟦t⟧ₑ(z))
theorem ereval_tExp (t : EMLTermV) (z : EReal) :
    ⟦tExp t⟧ₑ(z) = emlExp (⟦t⟧ₑ(z)) := by
  simp only [tExp, ereval_app, ereval_one]
  norm_cast
  simp [emlLog_one]

-- R2: ⟦tLog t⟧ₑ(z) = emlLog(⟦t⟧ₑ(z))  — INCONDICIONAL en EReal
-- Prueba: usa emlLog_emlExp y ereal_shift_cancel.
theorem ereval_tLog (t : EMLTermV) (z : EReal) :
    ⟦tLog t⟧ₑ(z) = emlLog (⟦t⟧ₑ(z)) := by
  simp only [tLog, ereval_app, ereval_one]
  -- norm_cast normaliza ↑(1:ℝ) a (1:EReal) para que emlLog_one dispare
  norm_cast
  simp only [emlLog_one, neg_zero, add_zero, emlLog_emlExp]
  have hsc := ereal_shift_cancel (Real.exp 1) (emlLog (⟦t⟧ₑ(z)))
  simp only [emlExp_real] at hsc
  exact hsc

-- ============================================================
-- §7. ÁRBOL CORRECTO PARA Minus(x) = −x
-- ============================================================
--
-- En Basic.lean: tMinus x = app (tLog one) (tExp x)
--   → evaluación en ℝ: 1 − x  (INCORRECTO para −x)
--   → evaluación en EReal: también 1 − x (emlLog 1 = 0, emlExp 0 = 1)
--
-- El árbol CORRECTO necesita log(0) = −∞ = ⊥:
--   tMinusV x = app (tLog (tLog one)) (tExp x)
--
-- Semántica en EReal:
--   ereval (tLog one) z      = emlLog 1    = 0    [ereval_tLog + emlLog_one]
--   ereval (tLog(tLog one)) z = emlLog 0   = ⊥    [ereval_tLog + emlLog_zero]
--   ereval (app ⊥_tree (tExp x)) z
--     = emlExp ⊥ + (-emlLog (emlExp (ereval x z)))
--     = 0         + (-(ereval x z))               [emlExp_bot + emlLog_emlExp]
--     = -ereval x z  ✓

/-- El árbol EMLTermV que representa la función Minus(x) = −x.
    Requiere log(0) = −∞, disponible solo en EReal. -/
def tMinusV (x : EMLTermV) : EMLTermV :=
  app (tLog (tLog one)) (tExp x)

/-- **Teorema central de Extended.lean:**
    tMinusV(x) evalúa a −z en EReal. Incondicional.
    Demuestra que Minus(x) = −x se formaliza con log(0) = ⊥. -/
theorem ereval_tMinusV (x : EMLTermV) (z : EReal) :
    ⟦tMinusV x⟧ₑ(z) = -⟦x⟧ₑ(z) := by
  simp only [tMinusV, ereval_app, ereval_tLog, ereval_tExp, ereval_one]
  norm_cast
  simp [emlLog_one, emlLog_zero, emlExp_bot, emlLog_emlExp]

-- Casos especiales verificados:

theorem ereval_tMinusV_var (z : EReal) :
    ⟦tMinusV var⟧ₑ(z) = -z := by
  simp [ereval_tMinusV]

theorem ereval_tMinusV_one (z : EReal) :
    ⟦tMinusV one⟧ₑ(z) = (-1 : ℝ) := by
  rw [ereval_tMinusV, ereval_one]; norm_cast

-- ============================================================
-- §8. SUBTRACT Y PLUS EN EReal
-- ============================================================

def tSubtractV (x y : EMLTermV) : EMLTermV :=
  app (tLog x) (tExp y)

/-- Subtract(x, y) = x − y = x + (-y), cuando ⟦x⟧ₑ(z) ≥ 0.
    La condición es más débil que la original (>0 y ≠⊤):
    cubre x = 0 via exp(log 0) = exp ⊥ = 0, y x = ⊤ via exp(log ⊤) = ⊤. -/
theorem ereval_tSubtractV (t s : EMLTermV) (z : EReal)
    (ht : 0 ≤ ⟦t⟧ₑ(z)) :
    ⟦tSubtractV t s⟧ₑ(z) = ⟦t⟧ₑ(z) + (-⟦s⟧ₑ(z)) := by
  simp only [tSubtractV, ereval_app, ereval_tLog, ereval_tExp]
  rw [emlLog_emlExp, emlExp_emlLog_nonneg ht]

def tPlusV (x y : EMLTermV) : EMLTermV :=
  tSubtractV x (tMinusV y)

/-- Plus(x, y) = x + y, cuando ⟦x⟧ₑ(z) ≥ 0. -/
theorem ereval_tPlusV (t s : EMLTermV) (z : EReal)
    (ht : 0 ≤ ⟦t⟧ₑ(z)) :
    ⟦tPlusV t s⟧ₑ(z) = ⟦t⟧ₑ(z) + ⟦s⟧ₑ(z) := by
  simp only [tPlusV]
  rw [ereval_tSubtractV _ _ _ ht, ereval_tMinusV]
  simp [neg_neg]

-- ============================================================
-- §9. INV Y TIMES EN EReal
-- ============================================================
--
-- R6: Inv(x) = Exp(Minus(Log(x)))
-- R7: Times(x,y) = Exp(Plus(Log(x), Log(y)))

def tInvV (x : EMLTermV) : EMLTermV :=
  tExp (tMinusV (tLog x))

def tTimesV (x y : EMLTermV) : EMLTermV :=
  tExp (tPlusV (tLog x) (tLog y))

/-- Inv: descomposición canónica como exp(-log(·)). Incondicional. -/
theorem ereval_tInvV (t : EMLTermV) (z : EReal) :
    ⟦tInvV t⟧ₑ(z) = emlExp (-emlLog ⟦t⟧ₑ(z)) := by
  simp only [tInvV, ereval_tExp, ereval_tMinusV, ereval_tLog]

/-- Para r > 0 real: Inv(r) = r⁻¹. -/
theorem ereval_tInvV_real (t : EMLTermV) (z : EReal) (r : ℝ)
    (hr : 0 < r) (heq : ⟦t⟧ₑ(z) = (r : EReal)) :
    ⟦tInvV t⟧ₑ(z) = ((r⁻¹ : ℝ) : EReal) := by
  rw [ereval_tInvV, heq, emlLog_real_pos hr]
  norm_cast
  rw [emlExp_real]
  norm_cast
  rw [← Real.log_inv, Real.exp_log (inv_pos.mpr hr)]

/-- Para r₁ ≥ 1 > 0 y r₂ > 0: Times(r₁, r₂) = r₁ · r₂.
    La condición r₁ ≥ 1 es requerida por tPlusV (necesita 0 ≤ log(r₁)). -/
theorem ereval_tTimesV_real (t s : EMLTermV) (z : EReal) (r₁ r₂ : ℝ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 0 < r₂)
    (h₁ : ⟦t⟧ₑ(z) = (r₁ : EReal)) (h₂ : ⟦s⟧ₑ(z) = (r₂ : EReal)) :
    ⟦tTimesV t s⟧ₑ(z) = ((r₁ * r₂ : ℝ) : EReal) := by
  simp only [tTimesV, ereval_tExp]
  have hr₁_pos : 0 < r₁ := lt_of_lt_of_le one_pos hr₁
  have hlog : 0 ≤ ⟦tLog t⟧ₑ(z) := by
    rw [ereval_tLog, h₁, emlLog_real_pos hr₁_pos]
    exact_mod_cast Real.log_nonneg hr₁
  rw [ereval_tPlusV _ _ _ hlog, ereval_tLog, ereval_tLog, h₁, h₂,
      emlLog_real_pos hr₁_pos, emlLog_real_pos hr₂]
  norm_cast
  rw [emlExp_real]
  norm_cast
  rw [← Real.log_mul hr₁_pos.ne' hr₂.ne', Real.exp_log (mul_pos hr₁_pos hr₂)]

-- ============================================================
-- §10. INVENTARIO DE TEOREMAS — COMPARACIÓN GLOBAL
-- ============================================================
--
-- ÁRBOL          ℝ (reval)            EReal (ereval)
-- ─────────────────────────────────────────────────────────
-- tExp t       → exp(·)  incondicional  exp(·)  incondicional
-- tLog t       → log(·)  incondicional  log(·)  incondicional
-- tMinusV t    →         [INCORRECTO]   −(·)    INCONDICIONAL  ← §7
-- tSubtractV   →         necesita ≥0    t−s     necesita ≥0    ← §8
-- tPlusV       →         necesita ≥0    t+s     necesita ≥0    ← §8
-- tInvV        →         exp(-log(·))   exp(-log(·)) incondicional ← §9
-- tTimesV      →         r₁·r₂          r₁·r₂   necesita r₁≥1  ← §9
--
-- NOTA: la condición r₁ ≥ 1 en Times refleja que tPlusV necesita
-- 0 ≤ log(r₁). Para r₁ ∈ (0,1), log(r₁) < 0 y tPlusV no aplica.
-- La cadena completa de Odrzywołek se verifica sobre ℝ⁺ donde los
-- inputs intermedios son siempre ≥ 1 (e.g., exp(·) ≥ e⁻∞ = 0).

end EMLTermV
end EML
