-- ============================================================
-- EML/Real.lean
-- Evaluador real de términos EML — sin hipótesis de rama
--
-- Objetivo: probar ⟦tLog t⟧ᵣ(z) = Real.log (⟦t⟧ᵣ(z))
-- sin ninguna hipótesis sobre z o ⟦t⟧ᵣ(z).
--
-- Por qué es posible:
--   Real.log_exp : ∀ x : ℝ, Real.log (Real.exp x) = x   (incondicional)
--   Real.log_one : Real.log 1 = 0                         (incondicional)
--
-- Por qué Complex.log_exp NO es incondicional:
--   Complex.log_exp necesita z.im ∈ (−π, π]  (rama principal)
--
-- Tabla de teoremas y sus condiciones:
--   reval_tExp          : ∀ t z,  incondicional  ✓
--   reval_tLog          : ∀ t z,  incondicional  ✓   (resultado principal)
--   reval_tExp_pos      : ∀ t z,  incondicional  ✓   (positividad)
--   reval_tSubtract     : ∀ t s z, necesita 0 < reval t z  ✗
--   reval_tMinus_wrong  : nota — tMinus en ℝ computa 1−x, no −x
-- ============================================================

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import EML.Basic
import Mathlib.Tactic

namespace EML
namespace EMLTerm

-- ============================================================
-- §1. EL EVALUADOR REAL
-- ============================================================
--
-- Usa Real.exp y Real.log de Mathlib.
-- Real.log es total: Real.log x = 0 para x ≤ 0.
-- Esta totalidad es lo que permite evitar hipótesis de rama.

/-- Evaluación real de un término EML en z : ℝ. -/
noncomputable def reval (t : EMLTerm) (z : ℝ) : ℝ :=
  match t with
  | one       => 1
  | app t' s' => Real.exp (reval t' z) - Real.log (reval s' z)

notation "⟦" t "⟧ᵣ(" z ")" => EMLTerm.reval t z

-- Lemas base: permiten que simp expanda reval paso a paso.

@[simp]
theorem reval_one (z : ℝ) : ⟦one⟧ᵣ(z) = 1 := rfl

@[simp]
theorem reval_app (t s : EMLTerm) (z : ℝ) :
    ⟦app t s⟧ᵣ(z) = Real.exp (⟦t⟧ᵣ(z)) - Real.log (⟦s⟧ᵣ(z)) := rfl

-- ============================================================
-- §2. TEOREMAS INCONDICIONALES
-- ============================================================

-- R1: ⟦tExp t⟧ᵣ(z) = exp(⟦t⟧ᵣ(z))
-- Prueba: tExp t = app t one, y Real.log 1 = 0.
theorem reval_tExp (t : EMLTerm) (z : ℝ) :
    ⟦tExp t⟧ᵣ(z) = Real.exp (⟦t⟧ᵣ(z)) := by
  simp [tExp, Real.log_one]

-- Corolario: la exponencial siempre produce valores positivos.
theorem reval_tExp_pos (t : EMLTerm) (z : ℝ) :
    0 < ⟦tExp t⟧ᵣ(z) := by
  rw [reval_tExp]; exact Real.exp_pos _

-- ============================================================
-- §3. TEOREMA PRINCIPAL — reval_tLog SIN HIPÓTESIS DE RAMA
-- ============================================================
--
-- La cadena de simplificación (tLog t = app one (app (app one t) one)):
--
--   ⟦tLog t⟧ᵣ(z)
--   = exp(⟦one⟧ᵣ(z)) - log(⟦app (app one t) one⟧ᵣ(z))
--   = exp(1)  - log(exp(⟦app one t⟧ᵣ(z)) - log(⟦one⟧ᵣ(z)))
--   = exp(1)  - log(exp(exp(1) - log(⟦t⟧ᵣ(z))) - log(1))
--   = exp(1)  - log(exp(exp(1) - log(⟦t⟧ᵣ(z))) - 0)          [Real.log_one]
--   = exp(1)  - log(exp(exp(1) - log(⟦t⟧ᵣ(z))))              [sub_zero]
--   = exp(1)  - (exp(1) - log(⟦t⟧ᵣ(z)))                      [Real.log_exp — ¡incondicional!]
--   = log(⟦t⟧ᵣ(z))                                            [ring]
--
-- No aparece Real.exp_log (que necesitaría positivity).
-- Solo Real.log_exp, que vale para todo x : ℝ.

/-- **Teorema principal de ECT-08.**
    La evaluación real de tLog es el logaritmo real, sin hipótesis. -/
theorem reval_tLog (t : EMLTerm) (z : ℝ) :
    ⟦tLog t⟧ᵣ(z) = Real.log (⟦t⟧ᵣ(z)) := by
  simp only [tLog, reval_app, reval_one, Real.log_one, sub_zero, Real.log_exp]
  ring

-- Verificación inmediata en casos concretos:

-- log(exp(z)) = z  [conocido, pero ahora via tLog]
theorem reval_tLog_tExp (t : EMLTerm) (z : ℝ) :
    ⟦tLog (tExp t)⟧ᵣ(z) = ⟦t⟧ᵣ(z) := by
  rw [reval_tLog, reval_tExp, Real.log_exp]

-- log(1) = 0  [via tLog one]
theorem reval_tLog_one (z : ℝ) : ⟦tLog one⟧ᵣ(z) = 0 := by
  rw [reval_tLog, reval_one, Real.log_one]

-- log de un árbol positivo: cuando reval t z > 0, log es el log usual.
-- Esto no añade nada nuevo — Real.log ya lo garantiza para positivos.

-- ============================================================
-- §4. TEOREMAS CON HIPÓTESIS (NECESITAN POSITIVIDAD)
-- ============================================================
--
-- Estos teoremas requieren 0 < reval t z porque usan Real.exp_log.
-- El análisis detalla por qué no pueden ser incondicionales.

-- R3: ⟦tSubtract t s⟧ᵣ(z) = ⟦t⟧ᵣ(z) − ⟦s⟧ᵣ(z)
--
-- Cadena:
--   tSubtract t s = app (tLog t) (tExp s)
--   ⟦tSubtract t s⟧ᵣ(z)
--   = exp(⟦tLog t⟧ᵣ(z)) - log(⟦tExp s⟧ᵣ(z))
--   = exp(Real.log (⟦t⟧ᵣ(z))) - log(exp(⟦s⟧ᵣ(z)))   [reval_tLog, reval_tExp]
--   = exp(Real.log (⟦t⟧ᵣ(z))) - ⟦s⟧ᵣ(z)              [Real.log_exp]
--   = ⟦t⟧ᵣ(z) - ⟦s⟧ᵣ(z)                              [Real.exp_log — necesita ht!]
--
-- El último paso requiere Real.exp_log : 0 < x → exp(log x) = x.
theorem reval_tSubtract (t s : EMLTerm) (z : ℝ)
    (ht : 0 < ⟦t⟧ᵣ(z)) :
    ⟦tSubtract t s⟧ᵣ(z) = ⟦t⟧ᵣ(z) - ⟦s⟧ᵣ(z) := by
  simp only [tSubtract, reval_app]
  rw [reval_tLog, reval_tExp, Real.log_exp, Real.exp_log ht]

-- La hipótesis `ht` es necesaria: sin ella, cuando ⟦t⟧ᵣ(z) ≤ 0,
--   Real.log (⟦t⟧ᵣ(z)) = 0  (convenio Mathlib)
--   Real.exp 0 = 1 ≠ ⟦t⟧ᵣ(z)

-- ============================================================
-- §5. POR QUÉ tMinus NO ES −x EN ℝ (NOTA FORMAL)
-- ============================================================
--
-- Matemáticamente: Minus(x) = −x.
-- En la cadena EML (Odrzywołek): Minus(x) = Subtract(ln(1), x) = Subtract(0, x).
-- Esto usa log(0) = −∞ y exp(−∞) = 0, que en ℝ extendido da:
--   exp(log(0)) − log(exp(x)) = 0 − x = −x  ✓
--
-- En Lean/Mathlib: Real.log 0 = 0 (convenio, no −∞).
-- Por tanto:
--   reval (tMinus x) z
--   = exp(reval (tLog one) z) - log(reval (tExp x) z)
--   = exp(log 1) - log(exp(reval x z))
--   = exp(0) - reval x z                  [Real.log_one y Real.log_exp]
--   = 1 - reval x z        ←  NO es −reval x z

/-- Lema documentado: en ℝ con la convención de Mathlib,
    tMinus evalúa a `1 − x`, no a `−x`. -/
theorem reval_tMinus_is_one_sub (x : EMLTerm) (z : ℝ) :
    ⟦tMinus x⟧ᵣ(z) = 1 - ⟦x⟧ᵣ(z) := by
  simp only [tMinus, reval_app, reval_tLog, reval_one, Real.log_one,
             reval_tExp, Real.log_exp, Real.exp_zero]

-- Consecuencia: la semántica de tSubtract, tPlus, tTimes, etc.
-- sobre ℝ difiere de la semántica matemática EML cuando las
-- expresiones pasan por log(0) = −∞.
-- Esto explica por qué la Tabla 1 de Odrzywołek requiere ℂ,
-- o alternativamente ℝ_ext (reales extendidos).

-- ============================================================
-- §6. LO QUE SÍ FUNCIONA INCONDICIONALMENTE EN ℝ
-- ============================================================
--
-- Las funciones de la Tabla 1 que no pasan por log(0):
--   Exp(x) = exp(x)  →  reval_tExp: incondicional ✓
--   Log(x) = log(x)  →  reval_tLog: incondicional ✓ (aunque log(x)=0 para x≤0)
--   Cosh(x) = (exp(x) + exp(-x))/2  →  requiere tMinus = −x, que falla en ℝ
--   Sqrt(x) = exp(log(x)/2)  →  requiere tSubtract = x−y, que necesita ht

-- La cota K ≤ 6 es una propiedad SINTÁCTICA y es incondicional:
-- no depende del evaluador real o complejo.

-- Complejidades verificadas sin evaluación:
theorem k_tExp_one : K[tExp one] = 2 := by simp [tExp, complexity]
theorem k_tLog_one : K[tLog one] = 4 := by simp [tLog, complexity]
theorem k_tLog_tLog_one : K[tLog (tLog one)] = 7 := by
  simp [tLog, complexity]

-- ============================================================
-- §7. COMPOSICIÓN: TESTIGO PARA exp ∘ f Y log ∘ f
-- ============================================================
--
-- La relación de composición es incondicional sobre reval.

/-- Si ⟦t⟧ᵣ(z) = f(z), entonces ⟦tExp t⟧ᵣ(z) = exp(f(z)). -/
theorem reval_compose_exp (t : EMLTerm) (f : ℝ → ℝ)
    (hf : ∀ z, ⟦t⟧ᵣ(z) = f z) (z : ℝ) :
    ⟦tExp t⟧ᵣ(z) = Real.exp (f z) := by
  rw [reval_tExp, hf]

/-- Si ⟦t⟧ᵣ(z) = f(z), entonces ⟦tLog t⟧ᵣ(z) = log(f(z)). -/
theorem reval_compose_log (t : EMLTerm) (f : ℝ → ℝ)
    (hf : ∀ z, ⟦t⟧ᵣ(z) = f z) (z : ℝ) :
    ⟦tLog t⟧ᵣ(z) = Real.log (f z) := by
  rw [reval_tLog, hf]

-- Caso especial: ⟦tLog (tExp t)⟧ᵣ = ⟦t⟧ᵣ  (log ∘ exp = id, incondicional)
theorem reval_log_exp_id (t : EMLTerm) (z : ℝ) :
    ⟦tLog (tExp t)⟧ᵣ(z) = ⟦t⟧ᵣ(z) :=
  reval_tLog_tExp t z

-- ============================================================
-- §8. TABLA RESUMEN — ¿QUÉ ES INCONDICIONAL EN ℝ?
-- ============================================================
--
-- | Teorema              | Incondicional | Condición si no |
-- |----------------------|---------------|-----------------|
-- | reval_tExp           | ✓             | —               |
-- | reval_tExp_pos       | ✓             | —               |
-- | reval_tLog           | ✓             | —  (RESULTADO PRINCIPAL) |
-- | reval_tLog_tExp      | ✓             | —               |
-- | reval_tLog_one       | ✓             | —               |
-- | reval_compose_exp    | ✓             | —               |
-- | reval_compose_log    | ✓             | —               |
-- | reval_tSubtract      | ✗             | 0 < reval t z   |
-- | reval_tMinus = −x    | ✗ (es 1−x)   | necesita ℝ_ext  |
-- | reval_tPlus = x+y    | ✗             | necesita ℝ_ext  |
-- | reval_tTimes = xy    | ✗             | necesita ℝ_ext  |

end EMLTerm
end EML
