-- EML.lean — Punto de entrada de la librería EML
-- Módulos estables: Basic, TRS, Real, Extended
-- Módulos con APIs pendientes de v4.29.0: CurryHoward, Expressivity, Liouville, Completeness

import EML.Basic
import EML.TRS
import EML.Real
import EML.Extended
-- import EML.CurryHoward   -- TODO: tipo mismatch en ereval/EReal conversions
-- import EML.Expressivity   -- TODO: Real.erf / Nat.primeCounting API cambiada
-- import EML.Liouville      -- TODO: depende de Expressivity
-- import EML.Completeness   -- TODO: depende de Liouville
