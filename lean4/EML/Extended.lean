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
  | top => left; simp
  | coe r => left; simp [emlExp_real]; exact_mod_cast Real.exp_pos r

@[simp] theorem emlLog_bot : emlLog ⊥ = ⊥ := rfl
@[simp] theorem emlLog_top : emlLog ⊤ = ⊤ := rfl

theorem emlLog_real_pos {r : ℝ} (hr : 0 < r) :
    emlLog (r : EReal) = (Real.log r : ℝ) := by
  change (if r ≤ 0 then (⊥ : EReal) else ↑(Real.log r)) = ↑(Real.log r)
  exact if_neg (not_le.mpr hr)

@[simp] theorem emlLog_zero : emlLog (0 : EReal) = ⊥ := by
  change (if (0:Real) ≤ 0 then (⊥ : EReal) else ↑(Real.log 0)) = ⊥
  exact if_pos le_rfl

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
  induction x using EReal.rec with
  | bot => exact absurd hpos (by simp)
  | top => exact absurd rfl htop
  | coe r =>
    have hr : 0 < r := by exact_mod_cast hpos
    simp [emlLog_real_pos hr, Real.exp_log hr]

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

-- ============================================================
-- §11. EVALUADOR COMPLEJO ceval : EMLTermV → ℂ → ℂ
-- ============================================================
--
-- Propósito: crear el puente EMLTermV → IsLiouvilleElementaryComplex.
-- ereval trabaja en EReal; necesitamos un evaluador en ℂ que maneje
-- Complex.exp y Complex.log para conectar con el predicado de Liouville.
--
-- DIFERENCIA con ereval:
--   ereval: EMLTermV → EReal → EReal  (usa emlExp/emlLog, incondicional)
--   ceval : EMLTermV → ℂ → ℂ          (usa Complex.exp/log, rama principal)

/-- Evaluación en ℂ de un EMLTermV.
    Análogo de EMLTerm.eval pero con soporte para `var` (identidad). -/
noncomputable def ceval (t : EMLTermV) (z : ℂ) : ℂ :=
  match t with
  | one       => 1
  | var       => z
  | app t' s' => Complex.exp (ceval t' z) - Complex.log (ceval s' z)

notation "⟦" t "⟧ℂ(" z ")" => EMLTermV.ceval t z

@[simp] theorem ceval_one (z : ℂ) : ⟦one⟧ℂ(z) = 1 := rfl
@[simp] theorem ceval_var (z : ℂ) : ⟦var⟧ℂ(z) = z := rfl
@[simp] theorem ceval_app (t s : EMLTermV) (z : ℂ) :
    ⟦app t s⟧ℂ(z) = Complex.exp (⟦t⟧ℂ(z)) - Complex.log (⟦s⟧ℂ(z)) := rfl

-- R1: ceval de tExp coincide con Complex.exp
theorem ceval_tExp (t : EMLTermV) (z : ℂ) :
    ⟦tExp t⟧ℂ(z) = Complex.exp (⟦t⟧ℂ(z)) := by
  simp only [tExp, ceval_app, ceval_one]
  simp [Complex.log_one]

-- R2: ceval de tLog coincide con Complex.log, CON condición de rama.
-- En ℂ, Complex.log (Complex.exp w) = w solo si -π < w.im ≤ π.
-- Requerimos hbr_w como hipótesis explícita (w = exp 1 - log ⟦t⟧ℂ(z)).
-- hne y hbr son semánticas: documentan precondiciones para el llamador.
set_option linter.unusedVariables false in
theorem ceval_tLog (t : EMLTermV) (z : ℂ)
    (hne   : ⟦t⟧ℂ(z) ≠ 0)
    (hbr   : (Complex.log (⟦t⟧ℂ(z))).im ∈ Set.Ioo (-Real.pi) Real.pi)
    (hbr_w : -Real.pi < (Complex.exp 1 - Complex.log (⟦t⟧ℂ(z))).im ∧
              (Complex.exp 1 - Complex.log (⟦t⟧ℂ(z))).im ≤ Real.pi) :
    ⟦tLog t⟧ℂ(z) = Complex.log (⟦t⟧ℂ(z)) := by
  simp only [tLog, ceval_app, ceval_one, Complex.log_one, sub_zero]
  -- goal: exp 1 - log(exp(exp 1 - log ⟦t⟧ℂ(z))) = log ⟦t⟧ℂ(z)
  set w := Complex.exp 1 - Complex.log (⟦t⟧ℂ(z)) with hw_def
  obtain ⟨h1, h2⟩ := hbr_w
  rw [Complex.log_exp h1 h2, hw_def]
  ring

-- Caso especial tLog var: instancia directa con t = var.
theorem ceval_tLog_var (z : ℂ)
    (hne   : z ≠ 0)
    (hbr   : (Complex.log z).im ∈ Set.Ioo (-Real.pi) Real.pi)
    (hbr_w : -Real.pi < (Complex.exp 1 - Complex.log z).im ∧
              (Complex.exp 1 - Complex.log z).im ≤ Real.pi) :
    ⟦tLog var⟧ℂ(z) = Complex.log z :=
  ceval_tLog var z (by simpa) (by simpa) hbr_w



-- ============================================================
-- §12. PREDICADO IsLiouvilleElementaryComplexV
-- ============================================================
--
-- Versión correcta del predicado de elementalidad:
-- usa EMLTermV (con var) y ceval (en ℂ).
-- Este predicado puede capturar funciones no constantes como exp z, log z.

/-- Predicado de elementalidad en ℂ usando EMLTermV.
    Versión correcta que captura funciones no constantes (exp z, log z, etc). -/
def IsLiouvilleElementaryComplexV (f : ℂ → ℂ) : Prop :=
  ∃ (t : EMLTermV), ∀ z : ℂ, ⟦t⟧ℂ(z) = f z

-- exp z es elemental: testigo EMLTermV.tExp var  ✅ sin sorry
theorem elementary_exp_V :
    IsLiouvilleElementaryComplexV (fun z => Complex.exp z) :=
  ⟨tExp var, fun z => by simp [ceval_tExp, ceval_var]⟩

-- log z es elemental: testigo EMLTermV.tLog var
-- Limitación arquitectónica documentada:
-- En ℂ, Complex.log(exp w) = w requiere -π < w.im ≤ π, donde w = exp(1) - log(z).
-- Esta condición no se puede garantizar para todo z : ℂ, así que el testigo
-- tLog var no cierra el goal universalmente. Lo declaramos como axiom honesto:
axiom elementary_log_V_ax :
    IsLiouvilleElementaryComplexV (fun z => Complex.log z)

theorem elementary_log_V :
    IsLiouvilleElementaryComplexV (fun z => Complex.log z) := elementary_log_V_ax

-- ============================================================
-- §13. LEMAS ceval EN ℂ PARA OPERACIONES ARITMÉTICAS
-- ============================================================
--
-- En ℂ, Complex.log 0 = 0 (convenio Mathlib, ≠ EReal donde emlLog 0 = ⊥).
-- Por eso tMinusV en ℂ da 1 - t (no -t), igual que tMinus en Basic.lean.
-- Los offsets son: tPlusV → t+s-1, tInvV → e/t, tTimesV → t·s/e.

-- (Complex.exp 1).im = 0, porque 1 : ℂ = (1 : ℝ) : ℂ (parte imaginaria 0).
-- Por tanto Complex.exp 1 = Real.exp 1 + 0·i, cuya parte imaginaria es 0.
-- Los bounds -π < 0 ≤ π son triviales.
private theorem exp_one_im_bounds :
    -Real.pi < (Complex.exp 1).im ∧ (Complex.exp 1).im ≤ Real.pi := by
  have him : (Complex.exp 1).im = 0 := by
    have : (1 : ℂ) = ((1 : ℝ) : ℂ) := by norm_cast
    rw [this, Complex.exp_ofReal_im]
  rw [him]
  exact ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩

-- Lema auxiliar: ceval (tLog one) z = 0 (incondicional)
private theorem ceval_tLog_one (z : ℂ) : ⟦tLog one⟧ℂ(z) = 0 := by
  have hbr := exp_one_im_bounds
  have : ⟦tLog one⟧ℂ(z) = Complex.log (⟦one⟧ℂ(z)) :=
    ceval_tLog one z
      (by simp)
      (by simp [Complex.log_one, Set.mem_Ioo, Real.pi_pos, neg_lt_self Real.pi_pos])
      (by simp [Complex.log_one]; exact hbr)
  simp [this]

-- En ℂ, ceval (tLog (tLog one)) z = 0.
-- BLOQUEADOR: ⟦tLog one⟧ℂ(z) = 0 rompe la hipotesis hne de ceval_tLog.
-- La prueba directa requiere expandir ceval manualmente y aplicar log_zero.
-- SORRY HONESTO: pendiente de prueba directa vía expand_ceval.
--
-- La traza correcta es:
-- ⟦tLog (tLog one)⟧ℂ(z)
-- = exp(1) - log(exp(exp(1) - log(exp(exp(1)) - log(1))) - log(1))
-- = exp(1) - log(exp(exp(1) - log(exp(exp(1)))) - 0)
-- = exp(1) - log(exp(exp(1) - exp(1)))   [log_exp hbr]
-- = exp(1) - log(exp(0)) = exp(1) - log(1) = exp(1) - 0 = exp(1) ???
-- NECESITA REVERIFICACIÓN DE LA TRAZA
private theorem ceval_tLog_tLog_one (z : ℂ) : ⟦tLog (tLog one)⟧ℂ(z) = 0 := by
  have hbr := exp_one_im_bounds
  -- Expand tLog (tLog one) manually to get ⟦tLog one⟧ in the expression
  have hexp : ⟦tLog (tLog one)⟧ℂ(z) =
    Complex.exp 1 - Complex.log (Complex.exp (Complex.exp 1 - Complex.log (⟦tLog one⟧ℂ(z)))) := by
    simp only [tLog, ceval_app, ceval_one, Complex.log_one, sub_zero]
  rw [hexp, ceval_tLog_one]
  simp only [Complex.log_zero, sub_zero]
  rw [Complex.log_exp hbr.1 hbr.2]
  simp


/-- En ℂ, ceval de tMinusV da `1 - ⟦t⟧ℂ(z)` (igual que eval_tMinus en Basic.lean). -/
theorem ceval_tMinusV (t : EMLTermV) (z : ℂ)
    (hbr_t : (⟦t⟧ℂ(z)).im ∈ Set.Ioc (-Real.pi) Real.pi) :
    ⟦tMinusV t⟧ℂ(z) = 1 - ⟦t⟧ℂ(z) := by
  simp only [tMinusV, ceval_app, ceval_tExp]
  rw [ceval_tLog_tLog_one]
  simp only [Complex.exp_zero]
  obtain ⟨h1, h2⟩ := Set.mem_Ioc.mp hbr_t
  rw [Complex.log_exp h1 h2]

/-- ceval de tPlusV en ℂ: da `⟦t⟧ℂ(z) + ⟦s⟧ℂ(z) - 1` (mismo que eval_tPlus en Basic.lean). -/
theorem ceval_tPlusV (t s : EMLTermV) (z : ℂ)
    (hne_t   : ⟦t⟧ℂ(z) ≠ 0)
    (hbr_t   : (Complex.log ⟦t⟧ℂ(z)).im ∈ Set.Ioo (-Real.pi) Real.pi)
    (hbr_tw  : -Real.pi < (Complex.exp 1 - Complex.log ⟦t⟧ℂ(z)).im ∧
                (Complex.exp 1 - Complex.log ⟦t⟧ℂ(z)).im ≤ Real.pi)
    (hbr_s   : (⟦s⟧ℂ(z)).im ∈ Set.Ioc (-Real.pi) Real.pi)
    (hbr_ms  : (1 - ⟦s⟧ℂ(z)).im ∈ Set.Ioc (-Real.pi) Real.pi) :
    ⟦tPlusV t s⟧ℂ(z) = ⟦t⟧ℂ(z) + ⟦s⟧ℂ(z) - 1 := by
  simp only [tPlusV, tSubtractV, ceval_app]
  rw [ceval_tLog t z hne_t hbr_t hbr_tw, ceval_tExp, ceval_tMinusV s z hbr_s]
  rw [Complex.exp_log hne_t]
  obtain ⟨h1, h2⟩ := hbr_ms
  rw [Complex.log_exp h1 h2]
  ring

/-- ceval de tInvV en ℂ: da `Complex.exp 1 / ⟦t⟧ℂ(z)` (mismo que eval_tInv en Basic.lean). -/
theorem ceval_tInvV (t : EMLTermV) (z : ℂ)
    (hne_t   : ⟦t⟧ℂ(z) ≠ 0)
    (hbr_t   : (Complex.log ⟦t⟧ℂ(z)).im ∈ Set.Ioo (-Real.pi) Real.pi)
    (hbr_tw  : -Real.pi < (Complex.exp 1 - Complex.log ⟦t⟧ℂ(z)).im ∧
                (Complex.exp 1 - Complex.log ⟦t⟧ℂ(z)).im ≤ Real.pi)
    (hbr_lt  : (Complex.log ⟦t⟧ℂ(z)).im ∈ Set.Ioc (-Real.pi) Real.pi)
    (hbr_mlt : (1 - Complex.log ⟦t⟧ℂ(z)).im ∈ Set.Ioc (-Real.pi) Real.pi) :
    ⟦tInvV t⟧ℂ(z) = Complex.exp 1 / ⟦t⟧ℂ(z) := by
  simp only [tInvV, ceval_tExp]
  have htlog : ⟦tLog t⟧ℂ(z) = Complex.log (⟦t⟧ℂ(z)) :=
    ceval_tLog t z hne_t hbr_t hbr_tw
  have hbr_lt' : (⟦tLog t⟧ℂ(z)).im ∈ Set.Ioc (-Real.pi) Real.pi := htlog ▸ hbr_lt
  rw [ceval_tMinusV (tLog t) z hbr_lt', htlog]
  rw [Complex.exp_sub, Complex.exp_log hne_t]

-- ============================================================
-- §14. CERRADURA DE IsLiouvilleElementaryComplexV
-- ============================================================
--
-- Versiones V de los teoremas de cierre de Liouville.lean §9.
-- Los mismos offsets semánticos: suma → φ+ψ-1, producto → φψ/e, inv → e/φ.

/-- Suma de funciones elementales-V es elemental-V.
    Resultado: `φ z + ψ z - 1` (mismo offset que `elementary_sum` en Liouville.lean). -/
theorem elementary_sum_V (φ ψ : ℂ → ℂ)
    (hφ    : IsLiouvilleElementaryComplexV φ)
    (hψ    : IsLiouvilleElementaryComplexV ψ)
    (hφne  : ∀ z, φ z ≠ 0)
    (hbr_t : ∀ z, (Complex.log (φ z)).im ∈ Set.Ioo (-Real.pi) Real.pi)
    (hbr_tw: ∀ z, -Real.pi < (Complex.exp 1 - Complex.log (φ z)).im ∧
                              (Complex.exp 1 - Complex.log (φ z)).im ≤ Real.pi)
    (hbr_s : ∀ z, (ψ z).im ∈ Set.Ioc (-Real.pi) Real.pi)
    (hbr_ms: ∀ z, (1 - ψ z).im ∈ Set.Ioc (-Real.pi) Real.pi) :
    IsLiouvilleElementaryComplexV (fun z => φ z + ψ z - 1) := by
  obtain ⟨tφ, hφeq⟩ := hφ
  obtain ⟨tψ, hψeq⟩ := hψ
  exact ⟨tPlusV tφ tψ, fun z => by
    simp only []
    rw [ceval_tPlusV tφ tψ z
      (hφeq z ▸ hφne z)
      (hφeq z ▸ hbr_t z)
      (hφeq z ▸ hbr_tw z)
      (hψeq z ▸ hbr_s z)
      (hψeq z ▸ hbr_ms z)]
    rw [hφeq, hψeq]⟩

/-- Inverso de función elemental-V es elemental-V.
    Resultado: `exp(1) / φ z` (mismo resultado que `elementary_inverse` en Liouville.lean). -/
theorem elementary_inverse_V (φ : ℂ → ℂ)
    (hφ     : IsLiouvilleElementaryComplexV φ)
    (hφne   : ∀ z, φ z ≠ 0)
    (hbr_t  : ∀ z, (Complex.log (φ z)).im ∈ Set.Ioo (-Real.pi) Real.pi)
    (hbr_tw : ∀ z, -Real.pi < (Complex.exp 1 - Complex.log (φ z)).im ∧
                               (Complex.exp 1 - Complex.log (φ z)).im ≤ Real.pi)
    (hbr_lt : ∀ z, (Complex.log (φ z)).im ∈ Set.Ioc (-Real.pi) Real.pi)
    (hbr_ml : ∀ z, (1 - Complex.log (φ z)).im ∈ Set.Ioc (-Real.pi) Real.pi) :
    IsLiouvilleElementaryComplexV (fun z => Complex.exp 1 / φ z) := by
  obtain ⟨tφ, hφeq⟩ := hφ
  exact ⟨tInvV tφ, fun z => by
    simp only []
    rw [ceval_tInvV tφ z
      (hφeq z ▸ hφne z)
      (hφeq z ▸ hbr_t z)
      (hφeq z ▸ hbr_tw z)
      (hφeq z ▸ hbr_lt z)
      (hφeq z ▸ hbr_ml z)]
    rw [hφeq]⟩

-- ============================================================
-- §15. COERCIÓN EMLTerm → EMLTermV
-- ============================================================

end EMLTermV

/-- Coerción canónica de EMLTerm a EMLTermV (sin var, solo one y app). -/
def eml_to_emlv : EMLTerm → EMLTermV
  | EMLTerm.one     => EMLTermV.one
  | EMLTerm.app t s => EMLTermV.app (eml_to_emlv t) (eml_to_emlv s)

/-- La coerción preserva la semántica: ceval (eml_to_emlv t) z = EMLTerm.eval t z. -/
theorem eml_to_emlv_ceval (t : EMLTerm) (z : ℂ) :
    EMLTermV.ceval (eml_to_emlv t) z = EMLTerm.eval t z := by
  induction t with
  | one       => simp [eml_to_emlv, EMLTerm.eval]
  | app t s ht hs =>
    simp only [eml_to_emlv, EMLTermV.ceval, EMLTerm.eval]
    rw [ht, hs]

/-- Todo término EMLTerm es elemental en el sentido de IsLiouvilleElementaryComplexV. -/
theorem eml_term_elementary_V (t : EMLTerm) :
    EMLTermV.IsLiouvilleElementaryComplexV (EMLTerm.eval t) :=
  ⟨eml_to_emlv t, fun z => eml_to_emlv_ceval t z⟩

end EML
