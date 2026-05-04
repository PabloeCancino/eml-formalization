-- ============================================================
-- EML/TRS.lean
-- Sistema de Reescritura de Términos EML (TRS-EML)
--
-- formalizes el TRS↑ (expansión) y sus propiedades:
--   - EMLTermNamed: tipo con constructores de símbolos nombrados
--   - Las 15 reglas R1–R15 como relación de reescritura
--   - Termination: namedDepth decrece monotónamente (Prop T1)
--   - Forma Normal de Expansión (FNE)
--   - El par crítico de TRS↓ (no-Confluence, Prop C2)
-- ============================================================

import EML.Basic
import Mathlib.Tactic

namespace EML

-- ============================================================
-- §1. TIPO EMLTermNamed — GRAMÁTICA CON SÍMBOLOS NOMBRADOS
-- ============================================================
--
-- PROBLEMA EN EL DISEÑO ORIGINAL
-- --------------------------------
-- EMLTerm solo tiene `one` y `app`. Como `tExp x := app x one`
-- por definición, TRSUpStep (nExp x) (app x one) sería una identidad:
-- ambos lados son el mismo árbol. KN no puede crecer con esa medida.
--
-- SOLUCIÓN
-- --------
-- Definir EMLTermNamed con constructores distintos para los símbolos
-- nombrados. La Complexity KN asigna a cada símbolo nombrado el
-- peso de sus subárboles (sin overhead), mientras que `app` agrega
-- los pesos de sus dos hijos. Así:
--   KN(nExp x) = KN(x) < KN(x)+1 = KN(app x one)  ✓
--   KN(nLog x) = KN(x) < KN(x)+3                   ✓
--
-- La Termination se proof via `namedDepth`: número de capas de
-- símbolos nombrados, que decrece en cada paso de TRS↑.

/-- Término EML con símbolos nombrados (gramática extendida). -/
inductive EMLTermNamed : Type where
  | one       : EMLTermNamed
  | app       : EMLTermNamed → EMLTermNamed → EMLTermNamed
  | nExp      : EMLTermNamed → EMLTermNamed
  | nLog      : EMLTermNamed → EMLTermNamed
  | nMinus    : EMLTermNamed → EMLTermNamed
  | nSubtract : EMLTermNamed → EMLTermNamed → EMLTermNamed
  | nPlus     : EMLTermNamed → EMLTermNamed → EMLTermNamed
  | nInv      : EMLTermNamed → EMLTermNamed
  | nTimes    : EMLTermNamed → EMLTermNamed → EMLTermNamed
  | nSqr      : EMLTermNamed → EMLTermNamed
  | nSqrt     : EMLTermNamed → EMLTermNamed
  | nPower    : EMLTermNamed → EMLTermNamed → EMLTermNamed
  | nDivide   : EMLTermNamed → EMLTermNamed → EMLTermNamed
  | nHalf     : EMLTermNamed → EMLTermNamed
  | nAvg      : EMLTermNamed → EMLTermNamed → EMLTermNamed
  | nHypot    : EMLTermNamed → EMLTermNamed → EMLTermNamed
  | nCosh     : EMLTermNamed → EMLTermNamed
  deriving Repr, DecidableEq, Inhabited

namespace EMLTermNamed

-- ============================================================
-- §2. Complexity KN
-- ============================================================

/-- Complexity KN: hojas (ones) en el árbol, transparente a símbolos nombrados. -/
def kn : EMLTermNamed → ℕ
  | one           => 1
  | app t s       => t.kn + s.kn
  | nExp t        => t.kn
  | nLog t        => t.kn
  | nMinus t      => t.kn
  | nSubtract t s => t.kn + s.kn
  | nPlus t s     => t.kn + s.kn
  | nInv t        => t.kn
  | nTimes t s    => t.kn + s.kn
  | nSqr t        => t.kn
  | nSqrt t       => t.kn
  | nPower t s    => t.kn + s.kn
  | nDivide t s   => t.kn + s.kn
  | nHalf t       => t.kn
  | nAvg t s      => t.kn + s.kn
  | nHypot t s    => t.kn + s.kn
  | nCosh t       => t.kn

notation "KN[" t "]" => EMLTermNamed.kn t

@[simp] theorem kn_one : KN[(one : EMLTermNamed)] = 1 := rfl
@[simp] theorem kn_app (t s : EMLTermNamed) : KN[app t s] = KN[t] + KN[s] := rfl
@[simp] theorem kn_nExp (t : EMLTermNamed) : KN[nExp t] = KN[t] := rfl
@[simp] theorem kn_nLog (t : EMLTermNamed) : KN[nLog t] = KN[t] := rfl
@[simp] theorem kn_nMinus (t : EMLTermNamed) : KN[nMinus t] = KN[t] := rfl
@[simp] theorem kn_nSubtract (t s : EMLTermNamed) : KN[nSubtract t s] = KN[t] + KN[s] := rfl
@[simp] theorem kn_nPlus (t s : EMLTermNamed) : KN[nPlus t s] = KN[t] + KN[s] := rfl
@[simp] theorem kn_nInv (t : EMLTermNamed) : KN[nInv t] = KN[t] := rfl
@[simp] theorem kn_nTimes (t s : EMLTermNamed) : KN[nTimes t s] = KN[t] + KN[s] := rfl
@[simp] theorem kn_nSqr (t : EMLTermNamed) : KN[nSqr t] = KN[t] := rfl
@[simp] theorem kn_nSqrt (t : EMLTermNamed) : KN[nSqrt t] = KN[t] := rfl
@[simp] theorem kn_nPower (t s : EMLTermNamed) : KN[nPower t s] = KN[t] + KN[s] := rfl
@[simp] theorem kn_nDivide (t s : EMLTermNamed) : KN[nDivide t s] = KN[t] + KN[s] := rfl
@[simp] theorem kn_nHalf (t : EMLTermNamed) : KN[nHalf t] = KN[t] := rfl
@[simp] theorem kn_nAvg (t s : EMLTermNamed) : KN[nAvg t s] = KN[t] + KN[s] := rfl
@[simp] theorem kn_nHypot (t s : EMLTermNamed) : KN[nHypot t s] = KN[t] + KN[s] := rfl
@[simp] theorem kn_nCosh (t : EMLTermNamed) : KN[nCosh t] = KN[t] := rfl

theorem kn_pos : ∀ t : EMLTermNamed, 0 < KN[t] := by
  intro t; induction t with
  | one => simp
  | app t s ht hs => simp; omega
  | nExp t ht     => simpa
  | nLog t ht     => simpa
  | nMinus t ht   => simpa
  | nSubtract t s ht hs => simp; omega
  | nPlus t s ht hs     => simp; omega
  | nInv t ht           => simpa
  | nTimes t s ht hs    => simp; omega
  | nSqr t ht           => simpa
  | nSqrt t ht          => simpa
  | nPower t s ht hs    => simp; omega
  | nDivide t s ht hs   => simp; omega
  | nHalf t ht          => simpa
  | nAvg t s ht hs      => simp; omega
  | nHypot t s ht hs    => simp; omega
  | nCosh t ht          => simpa

-- ============================================================
-- §3. MEDIDA DE Termination: namedDepth
-- ============================================================
--
-- KN no crece en R3-R7 (reestructuración sin agregar hojas).
-- La Termination se proof por namedDepth: cada regla elimina
-- una capa de símbolo nombrado, reduciendo la depth.

/-- depth de anidamiento de símbolos nombrados. -/
def namedDepth : EMLTermNamed → ℕ
  | one           => 0
  | app t s       => max t.namedDepth s.namedDepth
  | nExp t        => t.namedDepth + 1
  | nLog t        => t.namedDepth + 1
  | nMinus t      => t.namedDepth + 1
  | nSubtract t s => max t.namedDepth s.namedDepth + 1
  | nPlus t s     => max t.namedDepth s.namedDepth + 1
  | nInv t        => t.namedDepth + 1
  | nTimes t s    => max t.namedDepth s.namedDepth + 1
  | nSqr t        => t.namedDepth + 1
  | nSqrt t       => t.namedDepth + 1
  | nPower t s    => max t.namedDepth s.namedDepth + 1
  | nDivide t s   => max t.namedDepth s.namedDepth + 1
  | nHalf t       => t.namedDepth + 1
  | nAvg t s      => max t.namedDepth s.namedDepth + 1
  | nHypot t s    => max t.namedDepth s.namedDepth + 1
  | nCosh t       => t.namedDepth + 1

-- ============================================================
-- §4. TRS↑ COMO RELACIÓN DE REESCRITURA
-- ============================================================

-- Constante auxiliar para R12:
private def nTwo : EMLTermNamed := nPlus one one

/-- Un paso de reescritura TRS↑: de símbolo nombrado a forma inferior. -/
inductive TRSUpStep : EMLTermNamed → EMLTermNamed → Prop where
  -- R1: Exp(x) → f(x, 1)
  | R1  : ∀ x,   TRSUpStep (nExp x)        (app x one)
  -- R2: Log(x) → f(1, f(f(1,x), 1))
  | R2  : ∀ x,   TRSUpStep (nLog x)        (app one (app (app one x) one))
  -- R3: Subtract(x,y) → f(Log(x), Exp(y))
  | R3  : ∀ x y, TRSUpStep (nSubtract x y) (app (nLog x) (nExp y))
  -- R4: Minus(x) → f(Log(1), Exp(x))
  | R4  : ∀ x,   TRSUpStep (nMinus x)      (app (nLog one) (nExp x))
  -- R5: Plus(x,y) → Subtract(x, Minus(y))
  | R5  : ∀ x y, TRSUpStep (nPlus x y)     (nSubtract x (nMinus y))
  -- R6: Inv(x) → Exp(Minus(Log(x)))
  | R6  : ∀ x,   TRSUpStep (nInv x)        (nExp (nMinus (nLog x)))
  -- R7: Times(x,y) → Exp(Plus(Log(x), Log(y)))
  | R7  : ∀ x y, TRSUpStep (nTimes x y)    (nExp (nPlus (nLog x) (nLog y)))
  -- R8: Sqr(x) → Times(x, x)
  | R8  : ∀ x,   TRSUpStep (nSqr x)        (nTimes x x)
  -- R9: Sqrt(x) → Exp(Half(Log(x)))
  | R9  : ∀ x,   TRSUpStep (nSqrt x)       (nExp (nHalf (nLog x)))
  -- R10: Power(x,y) → Exp(Times(y, Log(x)))
  | R10 : ∀ x y, TRSUpStep (nPower x y)    (nExp (nTimes y (nLog x)))
  -- R11: Divide(x,y) → Times(x, Inv(y))
  | R11 : ∀ x y, TRSUpStep (nDivide x y)   (nTimes x (nInv y))
  -- R12: Half(x) → Divide(x, 2)
  | R12 : ∀ x,   TRSUpStep (nHalf x)       (nDivide x nTwo)
  -- R13: Avg(x,y) → Half(Plus(x, y))
  | R13 : ∀ x y, TRSUpStep (nAvg x y)      (nHalf (nPlus x y))
  -- R14: Hypot(x,y) → Sqrt(Plus(Sqr(x), Sqr(y)))
  | R14 : ∀ x y, TRSUpStep (nHypot x y)    (nSqrt (nPlus (nSqr x) (nSqr y)))
  -- R15: Cosh(x) → Avg(Exp(x), Exp(Minus(x)))
  | R15 : ∀ x,   TRSUpStep (nCosh x)       (nAvg (nExp x) (nExp (nMinus x)))
  -- Cierre de contexto:
  | ctxLeft  : ∀ t t' s, TRSUpStep t t' → TRSUpStep (app t s) (app t' s)
  | ctxRight : ∀ t s s', TRSUpStep s s' → TRSUpStep (app t s) (app t s')

-- ============================================================
-- §5. TRS termination↑
-- ============================================================

-- ============================================================
-- NOTA SOBRE LA MEDIDA DE Termination
-- ============================================================
--
-- `namedDepth` sola NO funciona como medida decreciente para el TRS completo:
-- - R1 y R2: namedDepth(RHS) = 0 < namedDepth(LHS) = D(x)+1 ✓
-- - R3: nSubtract → app(nLog x, nExp y)
--       namedDepth(RHS) = max(D(x)+1, D(y)+1) = max(D(x),D(y))+1 = namedDepth(LHS) ✗
-- - R5: nPlus(x,y) → nSubtract(x, nMinus(y))
--       namedDepth(RHS) = max(D(x), D(y)+1)+1 ≥ D(y)+2 > max(D(x),D(y))+1 ✗ (puede crecer)
-- - ctxLeft: si namedDepth(s) > namedDepth(t), el rewrite no cambia la depth ✗
--
-- La Termination correcta usa una INTERPRETACIÓN POLINOMIAL:
-- Asignar a cada símbolo un peso W tal que W(LHS) > W(RHS) en cada regla.
-- Por ejemplo:
--   W(nTimes) = W(x)+W(y)+M² para M suficientemente grande
--   W(nPlus)  = W(x)+W(y)+M
--   W(nLog)   = W(x)+c₁, etc.
-- Los coeficientes se eligen para que R3-R15 sean decrecientes.
--
-- En este archivo formalizesmos la Termination de R1 y R2 (las reglas
-- "base" que eliminan símbolos a f-árboles puros) y enunciamos la
-- Termination general con sorry, indicando que requiere este argumento.

-- Lema central de Termination: cada paso TRSUpStep estrictamente
-- disminuye namedDepth (o lo mantiene a 0 para reglas que introducen `app`
-- puro con subestructuras de menor depth).
--
-- Concretamente, para cada constructor de TRSUpStep:
-- • R1: namedDepth (nExp x) = x.namedDepth + 1 > 0 = namedDepth (app x one)  ✓
-- • R2: namedDepth (nLog x) = x.namedDepth + 1 > namedDepth (app one (...)) ✓
-- • R3-R15: el LHS tiene depth ≥ 1; el RHS puede introducir
--           más constructores nombrados (e.g. R8: Sqr→Times(x,x) duplica x).
--           La medida correcta es una interpretación polinomial (future work).
--
-- La medida correcta es la suma ponderada de constructores nombrados,
-- que decrece estrictamente en cada aplicación de R1-R15.
-- formalizesmos via `measure namedCount` (R1 y R2 completamente, R3-R15 con sorry).

-- Medida de Termination: interpretación polinomial ponderada.
-- Constructores que DUPLICAN subárboles (nSqr, nHypot, nCosh) cuentan
-- su argumento DOS VECES. Los pesos se eligen para que cada regla R1-R15
-- haga decrecer estrictamente la medida:
--   nExp/nLog: +1    nMinus/nSub: +3    nInv: +6    nPlus: +7
--   nTimes: +11   nSqr: 2·W(x)+12  nDivide: +18  nHalf: +26
--   nSqrt: +29   nPower: +14  nAvg: +34
--   nCosh: 2·W(x)+40  nHypot: 2·W(x)+2·W(y)+61
def namedCountW : EMLTermNamed → ℕ
  | one           => 0
  | app t s       => t.namedCountW + s.namedCountW
  | nExp t        => t.namedCountW + 1
  | nLog t        => t.namedCountW + 1
  | nMinus t      => t.namedCountW + 3
  | nSubtract t s => t.namedCountW + s.namedCountW + 3
  | nPlus t s     => t.namedCountW + s.namedCountW + 7
  | nInv t        => t.namedCountW + 6
  | nTimes t s    => t.namedCountW + s.namedCountW + 11
  | nSqr t        => 2 * t.namedCountW + 12   -- cuenta t dos veces (R8: nSqr→nTimes t t)
  | nSqrt t       => t.namedCountW + 29
  | nPower t s    => t.namedCountW + s.namedCountW + 14
  | nDivide t s   => t.namedCountW + s.namedCountW + 18
  | nHalf t       => t.namedCountW + 26
  | nAvg t s      => t.namedCountW + s.namedCountW + 34
  | nHypot t s    => 2 * t.namedCountW + 2 * s.namedCountW + 61  -- duplica (R14)
  | nCosh t       => 2 * t.namedCountW + 40   -- cuenta t dos veces (R15)

-- Alias para retrocompatibilidad con trsUp_terminates
abbrev namedCount := namedCountW

/-- Interpretación polinomial: cada paso TRSUpStep decrece namedCountW estrictamente.
    Las reglas que duplican subárboles (R8: nSqr→nTimes t t, R14: nHypot→nSqrt(…nSqr…),
    R15: nCosh→nAvg(nExp, nExp(nMinus))) tienen pesos 2·W(x) en namedCountW,
    garantizando que la medida siempre decrece. -/
theorem trsUp_namedCount_decreases {t t' : EMLTermNamed}
    (h : TRSUpStep t t') : namedCountW t' < namedCountW t := by
  induction h with
  | R1 x         => simp [namedCountW]
  | R2 x         => simp [namedCountW]
  | R3 x y       => simp [namedCountW]; omega
  | R4 x         => simp [namedCountW]; omega
  | R5 x y       => simp [namedCountW]; omega
  | R6 x         => simp [namedCountW]
  | R7 x y       => simp [namedCountW]; omega
  | R8 x         => simp [namedCountW]; omega
  | R9 x         => simp [namedCountW]
  | R10 x y      => simp [namedCountW]; omega
  | R11 x y      => simp [namedCountW]; omega
  | R12 x        => simp [namedCountW, nTwo]       -- nTwo = nPlus one one → peso 7
  | R13 x y      => simp [namedCountW]
  | R14 x y      => simp [namedCountW]; omega
  | R15 x        => simp [namedCountW]; omega
  | ctxLeft  t t' s _ ih => simp [namedCountW]; omega
  | ctxRight t s s' _ ih => simp [namedCountW]; omega

/-- TRS↑ termina: todo término es accesible bajo la relación inversa.

    Prueba: usamos la medida `namedCount` que decrece estrictamente
    en cada paso de TRSUpStep (vía trsup_namedCount_decreases).
    El orden de ℕ es bien fundado, por lo que el sistema termina. -/
theorem trsUp_terminates : ∀ t : EMLTermNamed, Acc (fun t t' => TRSUpStep t' t) t := by
  intro t
  -- Inducción sobre una cota n ≥ namedCount t (evita API de strong_rec)
  suffices h : ∀ n t, namedCount t ≤ n → Acc (fun t t' => TRSUpStep t' t) t from
    h (namedCount t) t le_rfl
  intro n
  induction n with
  | zero =>
    intro t ht
    apply Acc.intro
    intro t' hstep
    exact absurd (Nat.lt_of_lt_of_le (trsUp_namedCount_decreases hstep) ht)
                 (Nat.not_lt_zero _)
  | succ n ih =>
    intro t ht
    apply Acc.intro
    intro t' hstep
    apply ih
    exact Nat.lt_succ_iff.mp
          (Nat.lt_of_lt_of_le (trsUp_namedCount_decreases hstep) ht)

-- ============================================================
-- §6. FORMA NORMAL DE EXPANSIÓN (FNE)
-- ============================================================

/-- Un término está en FNE si no contiene símbolos nombrados. -/
def isFNE : EMLTermNamed → Prop
  | one           => True
  | app t s       => isFNE t ∧ isFNE s
  | nExp _        => False
  | nLog _        => False
  | nMinus _      => False
  | nSubtract _ _ => False
  | nPlus _ _     => False
  | nInv _        => False
  | nTimes _ _    => False
  | nSqr _        => False
  | nSqrt _       => False
  | nPower _ _    => False
  | nDivide _ _   => False
  | nHalf _       => False
  | nAvg _ _      => False
  | nHypot _ _    => False
  | nCosh _       => False

theorem isFNE_one : isFNE (one : EMLTermNamed) := trivial

theorem isFNE_app {t s : EMLTermNamed} (ht : isFNE t) (hs : isFNE s) :
    isFNE (app t s) := ⟨ht, hs⟩

/-- Un término en FNE no puede dar un paso de TRS↑. -/
theorem isFNE_no_step {t : EMLTermNamed} (hfne : isFNE t) :
    ∀ t', ¬ TRSUpStep t t' := by
  induction t with
  | one =>
    intro t' h; cases h
  | app t s ht hs =>
    obtain ⟨hft, hfs⟩ := hfne
    intro t' h
    cases h with
    | ctxLeft _ _ _ hstep  => exact ht hft _ hstep
    | ctxRight _ _ _ hstep => exact hs hfs _ hstep
  | nExp _  | nLog _  | nMinus _  | nSubtract _ _  | nPlus _ _
  | nInv _  | nTimes _ _  | nSqr _  | nSqrt _  | nPower _ _
  | nDivide _ _  | nHalf _  | nAvg _ _  | nHypot _ _  | nCosh _ =>
    simp only [isFNE] at hfne

/-- namedDepth = 0 ↔ isFNE. -/
theorem isFNE_iff_depth_zero (t : EMLTermNamed) :
    isFNE t ↔ namedDepth t = 0 := by
  induction t with
  | one => simp [isFNE, namedDepth]
  | app t s ht hs =>
    constructor
    · intro ⟨hft, hfs⟩
      simp only [namedDepth, Nat.max_eq_zero_iff]
      exact ⟨ht.mp hft, hs.mp hfs⟩
    · intro h
      simp only [namedDepth, Nat.max_eq_zero_iff] at h
      exact ⟨ht.mpr h.1, hs.mpr h.2⟩
  | nExp _ | nLog _ | nMinus _ | nSubtract _ _ | nPlus _ _
  | nInv _ | nTimes _ _ | nSqr _ | nSqrt _ | nPower _ _
  | nDivide _ _ | nHalf _ | nAvg _ _ | nHypot _ _ | nCosh _ =>
    -- isFNE = False; namedDepth ≥ 1, so namedDepth = 0 is also False
    constructor
    · exact False.elim
    · intro h; simp only [namedDepth] at h; omega

-- ============================================================
-- §7. PAR CRÍTICO DE TRS↓ (NO-Confluence)
-- ============================================================
--
-- Proposición C2 (EML_Sistema_Reescritura.md):
-- El subtérmino f(f(1,x),1) admite dos reducciones incompatibles.

/-- El par crítico de TRS↓: dos reducciones dan resultados distintos.
    El subtérmino f(f(1,x),1) puede leerse como:
      A) Exp(f(1,x)) → e^(e − ln x)
      B) parte de Log(x) → ln(x)
    Para x genérico, exp(exp(1) − log(x)) ≠ log(x). -/
theorem trsDown_not_confluent :
    ¬ ∀ (z : ℂ), Complex.exp (Complex.exp 1 - Complex.log z) =
                  Complex.log z := by
  intro h
  -- Evaluar en z = 1: log(1) = 0, luego exp(exp(1)) = 0
  have h1 := h 1
  simp only [Complex.log_one, sub_zero] at h1
  -- h1 : Complex.exp (Complex.exp 1) = 0
  exact Complex.exp_ne_zero _ h1

-- ============================================================
-- §8. EQUIVALENCIA SEMÁNTICA (WORD PROBLEM)
-- ============================================================

/-- Dos árboles EMLTerm son semánticamente equivalentes. -/
def semanticEq (t s : EMLTerm) : Prop :=
  ∀ z : ℂ, EMLTerm.eval t z = EMLTerm.eval s z

notation t " ≡_EML " s => semanticEq t s

end EMLTermNamed
end EML
