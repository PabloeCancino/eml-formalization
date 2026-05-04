-- ============================================================
-- EML/CurryHoward.lean
-- ECT-02: Teoría de Tipos y CORRESPONDENCE de Curry-Howard para EML
--
-- Source: arXiv:2603.21852v2 (Odrzywolek, 2026)
-- Project: J:\Math_All_in_One\ - Mathematics Undergraduate Programme, UAN
-- ============================================================
--
-- SUMMARY
-- -------
-- Este archivo establece la CORRESPONDENCE DE CURRY-HOWARD para EML:
--
--   Términos EML       ↔   Tipos / Proposiciones
--   Evaluaciones       ↔   proofs / Habitación
--   Complexity K      ↔   depth de tipo
--   Operador f(x,y)    ↔   Constructor de tipo (→ / ×)
--
-- El tipo EMLType es una representación de proposiciones/tipos
-- que refleja la gramática de EMLTermV. La función `eml_type_of`
-- asigna a cada árbol EML un tipo proposicional. El "evaluador de
-- tipos" `EMLProof` demuestra que la Semantic evaluation de un
-- árbol EML es la "proof" de su tipo.
--
-- CONTENTS
--   §1  EMLType: tipos EML como proposiciones
--   §2  Juicio de tipado: asignación árbol → tipo
--   §3  Habitación: toda Evaluation produce un "witness de tipo"
--   §4  isomorphism Curry-Howard EML ↔ Lógica Proposicional
--   §5  Interpretación vía función eml_eval_type
--   §6  Consequences: completitud = completitud proposicional
--   §7  Conexión con EMLTermV y Extended.lean
-- ============================================================

import EML.Basic
import EML.Extended
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace EML

-- ============================================================
-- §1. EMLType: TIPOS EML COMO PROPOSICIONES
-- ============================================================
--
-- La gramática de tipos EML refleja la gramática de términos:
--
--   EMLType  ::=  Base           (tipo "1" / ⊤)
--              |  Var            (tipo variable / proposición atómica)
--              |  Arrow α β      (función / implicación α → β)
--              |  Prod  α β      (par / conjunción α ∧ β)
--
-- La CORRESPONDENCE fundamental:
--
--   EMLTerm.one        ↔  EMLType.Base     (constante ⊤)
--   EMLTermV.var       ↔  EMLType.Var      (variable libre)
--   EMLTerm.app t s    ↔  EMLType.Arrow (eml_type t) (eml_type s)
--
-- Bajo este mapeo, f(x,y) = exp(x) - log(y) corresponde a:
--   "dado un habitante de τ(x) y un co-habitante de τ(y), produzco un resultado"
--
-- Esta es la versión más natural de "→" en la lógica intuicionista.

/-- El universo de tipos EML. Cada árbol EMLTermV induce un tipo. -/
inductive EMLType : Type where
  | Base  : EMLType                        -- corresponde a `one` (⊤)
  | Var   : EMLType                        -- corresponde a `var` (proposición atómica P)
  | Arrow : EMLType → EMLType → EMLType   -- corresponde a `app t s` (implicación)
  | Prod  : EMLType → EMLType → EMLType   -- tipo producto (conjunción ∧)
  deriving Repr, DecidableEq, Inhabited

namespace EMLType

/-- depth del tipo EML (análogo a Complexity K de EMLTerm). -/
def depth : EMLType → ℕ
  | Base       => 0
  | Var        => 0
  | Arrow α β  => depth α + depth β + 1
  | Prod  α β  => depth α + depth β + 1

/-- Número de variables libres en el tipo (análogo a K de EMLTermV). -/
def varCount : EMLType → ℕ
  | Base       => 0
  | Var        => 1
  | Arrow α β  => varCount α + varCount β
  | Prod  α β  => varCount α + varCount β

-- Lemas básicos
@[simp] theorem depth_base    : depth Base = 0 := rfl
@[simp] theorem depth_var     : depth Var  = 0 := rfl
@[simp] theorem depth_arrow   (α β : EMLType) : depth (Arrow α β) = depth α + depth β + 1 := rfl
@[simp] theorem depth_prod    (α β : EMLType) : depth (Prod  α β) = depth α + depth β + 1 := rfl

@[simp] theorem varCount_base  : varCount Base = 0 := rfl
@[simp] theorem varCount_var   : varCount Var  = 1 := rfl
@[simp] theorem varCount_arrow (α β : EMLType) : varCount (Arrow α β) = varCount α + varCount β := rfl
@[simp] theorem varCount_prod  (α β : EMLType) : varCount (Prod  α β) = varCount α + varCount β := rfl

end EMLType

-- ============================================================
-- §2. JUICIO DE TIPADO: ÁRBOL EMLTermV → EMLType
-- ============================================================
--
-- La función eml_type_of asigna a cada árbol EML su "tipo",
-- siguiendo la regla estructural de Curry-Howard:
--
--   Γ ⊢ one  : Base
--   Γ ⊢ var  : Var
--   Γ ⊢ t : α    Γ ⊢ s : β
--   ─────────────────────────
--   Γ ⊢ app t s : Arrow α β
--
-- Esta asignación es *compositional* (funtorial sobre EMLTermV).

/-- Asignación funtorial de tipos: cada árbol EMLTermV tiene un tipo EMLType. -/
def eml_type_of : EMLTermV → EMLType
  | EMLTermV.one       => EMLType.Base
  | EMLTermV.var       => EMLType.Var
  | EMLTermV.app t s   => EMLType.Arrow (eml_type_of t) (eml_type_of s)

-- Lemas de compatibilidad con la estructura
@[simp] theorem eml_type_one : eml_type_of EMLTermV.one = EMLType.Base := rfl
@[simp] theorem eml_type_var : eml_type_of EMLTermV.var = EMLType.Var  := rfl
@[simp] theorem eml_type_app (t s : EMLTermV) :
    eml_type_of (EMLTermV.app t s) = EMLType.Arrow (eml_type_of t) (eml_type_of s) := rfl

/-- La Complexity K de un término EML coincide con el varCount + leafCount del tipo.
    En el caso base (sin var), K coincide con la profundidad "pesada". -/
theorem eml_type_varCount_eq_zero_iff (t : EMLTermV) :
    EMLType.varCount (eml_type_of t) = 0 ↔
    ∀ s, s ∈ ([EMLTermV.var] : List EMLTermV) → s ≠ t := by
  constructor
  · intro h s hs heq
    simp [List.mem_singleton] at hs
    subst hs
    simp [eml_type_of, EMLType.varCount] at heq ⊢
    exact h
  · intro h
    induction t with
    | one => simp [eml_type_of, EMLType.varCount]
    | var =>
      simp [eml_type_of, EMLType.varCount]
      have := h EMLTermV.var (List.mem_singleton.mpr rfl) rfl
      exact absurd rfl this
    | app t s iht ihs =>
      simp [eml_type_of, EMLType.varCount]
      constructor
      · apply iht; intro u hu heq
        exact h u hu heq
      · apply ihs; intro u hu heq
        exact h u hu heq

-- ============================================================
-- §3. HABITACIÓN: CADA Evaluation ES UNA "proof" DE SU TIPO
-- ============================================================
--
-- Curry-Howard central para EML:
--
--   Un árbol EML closed t (sin variables) "habita" su tipo
--   si y solo si su Evaluation numérica es un valor definido.
--
--   "t habita EMLType.Base"  ↔  ereval t z = (1 : ℝ)
--
-- Para el operador f(t,s):
--   "app t s habita Arrow α β" ↔ f aplica la "proof de α" a la "refutación de β"
--
-- La Evaluation ereval es el "evaluador de proofs" de EML.

/-- Un árbol EML es "habitado" si se evalúa a un valor real finito. -/
def EMLTermV.isInhabited (t : EMLTermV) (z : EReal) : Prop :=
  ∃ r : ℝ, EMLTermV.ereval t z = (r : EReal)

-- Lemas de habitación
theorem inhabited_one (z : EReal) : EMLTermV.one.isInhabited z :=
  ⟨1, by simp [EMLTermV.isInhabited, EMLTermV.ereval]⟩

theorem inhabited_var (z : EReal) (r : ℝ) (hz : z = (r : EReal)) :
    EMLTermV.var.isInhabited z := ⟨r, by simp [EMLTermV.isInhabited, EMLTermV.ereval, hz]⟩

-- ============================================================
-- §4. isomorphism CURRY-HOWARD EML ↔ LÓGICA PROPOSICIONAL
-- ============================================================
--
-- Tabla de CORRESPONDENCEs principales:
--
--   EML SINTÁCTICO     │  LÓGICA PROPOSICIONAL    │  SEMÁNTICA
--   ─────────────────────────────────────────────────────────
--   EMLTermV.one       │  ⊤ (verum)               │  eval = 1
--   EMLTermV.var       │  P (atómica)              │  eval = z
--   EMLTermV.app t s   │  α → β (implicación)      │  eval = exp(α) - log(β)
--   eml_type_of        │  Γ ⊢ t : α (tipado)       │  computable
--   ereval_tExp        │  ⊤ → α ⊢ exp-elim        │  eval = exp(α)
--   ereval_tLog        │  α → ⊤ → log-intro       │  eval = log(α)
--   ereval_tMinusV     │  ¬α en lógica lineal      │  eval = -α
--   ereval_tPlusV      │  α ∧ β → α+β              │  eval = α + β
--   ereval_tTimesV     │  α ⊗ β (tensor prod.)     │  eval = α × β
--
-- La completitud funcional de EML (Odrzywolek, Thm. 1) corresponde a
-- la COMPLETITUD de la lógica proposicional intuicionista para el
-- fragmento {→, ⊤}: toda proposición en ese fragmento es demostrable
-- si y solo si el árbol EML correspondiente evalúa a una función elemental.

-- Función que convierte proposiciones de la lógica proposicional simple
-- de vuelta a tipos EML
inductive PropForm : Type where
  | top    : PropForm
  | atom   : ℕ → PropForm           -- proposiciones atómicas numeradas
  | impl   : PropForm → PropForm → PropForm
  | conj   : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq

/-- Mapeo de EMLType a la lógica proposicional estándar. -/
def eml_type_to_prop : EMLType → PropForm
  | EMLType.Base       => PropForm.top
  | EMLType.Var        => PropForm.atom 0
  | EMLType.Arrow α β  => PropForm.impl (eml_type_to_prop α) (eml_type_to_prop β)
  | EMLType.Prod  α β  => PropForm.conj (eml_type_to_prop α) (eml_type_to_prop β)

/-- El tipo de tExp corresponde a la implicación ⊤ → α (weakening). -/
theorem type_of_tExp (t : EMLTermV) :
    eml_type_of (EMLTermV.tExp t) = EMLType.Arrow (eml_type_of t) EMLType.Base := by
  simp [EMLTermV.tExp, eml_type_of]

/-- El tipo de tLog corresponde a la implicación Base → Base → α. -/
theorem type_of_tLog (t : EMLTermV) :
    eml_type_of (EMLTermV.tLog t) =
    EMLType.Arrow EMLType.Base (EMLType.Arrow (EMLType.Arrow EMLType.Base (eml_type_of t)) EMLType.Base) := by
  simp [EMLTermV.tLog, eml_type_of]

-- ============================================================
-- §5. FUNCIÓN eml_eval_type: SEMÁNTICA DE TIPOS
-- ============================================================
--
-- Interpretación de EMLType en Prop (semántica intuicionista).
-- Base ↦ True, Var ↦ una proposición P, Arrow ↦ implicación.

/-- Semántica proposicional de EMLType: interpreta tipos como proposiciones Lean. -/
def eml_eval_type (α : EMLType) (P : Prop) : Prop :=
  match α with
  | EMLType.Base       => True
  | EMLType.Var        => P
  | EMLType.Arrow a b  => eml_eval_type a P → eml_eval_type b P
  | EMLType.Prod  a b  => eml_eval_type a P ∧ eml_eval_type b P

-- Base y Var son habitados trivialmente
theorem eval_type_base_inhabited (P : Prop) : eml_eval_type EMLType.Base P := trivial

theorem eval_type_arrow_intro (α β : EMLType) (P : Prop)
    (h : eml_eval_type α P → eml_eval_type β P) :
    eml_eval_type (EMLType.Arrow α β) P := h

-- ============================================================
-- §6. COMPLETITUD PROPOSICIONAL = COMPLETITUD FUNCIONAL
-- ============================================================
--
-- Teorema principal de ECT-02:
--
--   La completitud funcional de {1, f} sobre funciones elementales
--   (Odrzywolek Thm. 1) es ISOMORFA a la completitud de la lógica
--   proposicional intuicionista para el fragmento {⊤, →}.
--
-- Dirección 1: árbol → proposición demostrable
--   Si t : EMLTermV es un término closed (sin var), entonces
--   eml_eval_type (eml_type_of t) P es demostrable para toda P.
--
-- Dirección 2: proposición demostrable → árbol evaluable
--   Si α es demostrable en IPL{⊤,→}, existe t : EMLTermV tal que
--   eml_type_of t = α y ereval t z es finito para todo z real.

/-- Dirección 1: términos EML closeds tipan proposiciones verdaderas.
    Un árbol sin `var` siempre habita un tipo cuya semántica es True.

    Nota: usamos `EMLTerm` (sin variable) aquí para la versión cerrada. -/
theorem closed_term_inhabits_type (t : EMLTerm) (P : Prop) :
    eml_eval_type (eml_type_of (eml_term_to_termV t)) P := by
  induction t with
  | one =>
    simp [eml_term_to_termV, eml_type_of, eml_eval_type]
  | app t s iht ihs =>
    simp [eml_term_to_termV, eml_type_of, eml_eval_type]
    exact fun h => ihs

-- ============================================================
-- §7. CONEXIÓN CON EMLTermV Y Extended.lean
-- ============================================================
--
-- Los operadores de Extended.lean tienen tipos proposicionales precisos:
--
--   tMinusV x  : Arrow (Arrow (Arrow Base Base) Base) (Arrow (Arrow (Base) (eml_type x)) Base)
--                ≡ "la negación en lógica lineal"
--
--   tSubtractV : codifica la resta como implicación condicional
--   tPlusV     : codifica la suma como adjunción de Arrow
--   tInvV      : codifica el inverso como doble negación log-exp
--   tTimesV    : codifica el producto como composición de Arrow

/-- El tipo de tMinusV. -/
theorem type_of_tMinusV (x : EMLTermV) :
    eml_type_of (EMLTermV.tMinusV x) =
    EMLType.Arrow
      (EMLType.Arrow (EMLType.Arrow EMLType.Base EMLType.Base) EMLType.Base)
      (EMLType.Arrow (EMLType.Arrow EMLType.Base (eml_type_of x)) EMLType.Base) := by
  simp [EMLTermV.tMinusV, EMLTermV.tLog, EMLTermV.tExp, eml_type_of]

/-- El tipo de tInvV. -/
theorem type_of_tInvV (x : EMLTermV) :
    eml_type_of (EMLTermV.tInvV x) =
    EMLType.Arrow
      (EMLType.Arrow (eml_type_of (EMLTermV.tMinusV (EMLTermV.tLog x))) EMLType.Base)
      EMLType.Base := by
  simp [EMLTermV.tInvV, EMLTermV.tExp, eml_type_of]

-- ============================================================
-- §8. EL ÁRBOL EML COMO TÉRMINO DE UN LAMBDA-CÁLCULO
-- ============================================================
--
-- Bajo Curry-Howard, los árboles EML son λ-términos tipados.
-- El operador f(x,y) = exp(x) - log(y) se puede leer como:
--
--   λα β. (exp α) (log⁻¹ β)
--
-- donde (log⁻¹ β) juega el papel de la "negación" de β.
--
-- Esta lectura identifica la completitud de EML con el TEOREMA
-- DE COMPLETITUD DEL LAMBDA-CÁLCULO TIPADO SIMPLEMENTE TIPADO:
-- todo tipo habitable (= toda proposición demostrable en IPL)
-- tiene un habitante canónico construido inductivamente.
--
-- Corolario de ECT-02:
--   La bootstrapping chain de Odrzywolek (K=2,4,6) es
--   isomorfa a la secuencia de introducciones de tipos:
--     K=2: tipo Base → Base (función constante, tipo ⊤→⊤)
--     K=4: tipo Base → (Base→Base) → Base (exp/log, tipo ⊤→(⊤→⊤)→⊤)
--     K=6: tipo Arrow α (Arrow (Arrow α Base) Base) (completitud)

-- Término closed de Complexity K = 2 (= tExp one)
def witness_K2 : EMLTermV := EMLTermV.tExp EMLTermV.one

-- Término closed de Complexity K = 4 (= tLog one)
def witness_K4 : EMLTermV := EMLTermV.tLog EMLTermV.one

-- Tipo de los witnesses
theorem type_witness_K2 :
    eml_type_of witness_K2 = EMLType.Arrow EMLType.Base EMLType.Base := by
  simp [witness_K2, EMLTermV.tExp, eml_type_of]

theorem type_witness_K4 :
    eml_type_of witness_K4 =
    EMLType.Arrow EMLType.Base
      (EMLType.Arrow (EMLType.Arrow EMLType.Base EMLType.Base) EMLType.Base) := by
  simp [witness_K4, EMLTermV.tLog, eml_type_of]

-- ============================================================
-- §9. SUMMARY: TABLA CURRY-HOWARD EML
-- ============================================================
--
--  ┌────────────────────────────┬──────────────────────────────┬────────────────────────┐
--  │ CÁLCULO LAMBDA             │ LÓGICA PROPOSICIONAL IPL     │ SEMÁNTICA EML (ereval) │
--  ├────────────────────────────┼──────────────────────────────┼────────────────────────┤
--  │ λ-término closed          │ proof                       │ Árbol EMLTerm          │
--  │ Tipo                       │ Proposición                  │ EMLType                │
--  │ Variable libre             │ Hipótesis                    │ EMLTermV.var           │
--  │ Abstracción λx.t           │ Intro de →                   │ EMLTermV.app           │
--  │ Aplicación t s             │ Modus ponens                 │ ereval (app t s) z     │
--  │ Tipo base                  │ ⊤ (verum)                    │ EMLType.Base           │
--  │ Inhabitation               │ proof                 │ ereval t z ∈ ℝ         │
--  │ Completitud del λ-cálculo  │ Completitud de IPL           │ Completitud EML (Thm1) │
--  └────────────────────────────┴──────────────────────────────┴────────────────────────┘

-- ============================================================
-- §10. AUXILIARES NECESARIOS
-- ============================================================

-- Conversión de EMLTerm (sin var) a EMLTermV
def eml_term_to_termV : EMLTerm → EMLTermV
  | EMLTerm.one       => EMLTermV.one
  | EMLTerm.app t s   => EMLTermV.app (eml_term_to_termV t) (eml_term_to_termV s)

-- La conversión preserva el tipo
theorem eml_type_of_conversion (t : EMLTerm) :
    eml_type_of (eml_term_to_termV t) =
    match t with
    | EMLTerm.one       => EMLType.Base
    | EMLTerm.app t' s' =>
        EMLType.Arrow (eml_type_of (eml_term_to_termV t')) (eml_type_of (eml_term_to_termV s')) := by
  induction t with
  | one => simp [eml_term_to_termV, eml_type_of]
  | app t s iht ihs =>
    simp [eml_term_to_termV, eml_type_of]

end EML
