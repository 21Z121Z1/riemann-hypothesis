import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.EulDefs
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.GP

def xR (x : IdeleGroup ℚ) : ℝˣ := Units.map eR.toRingHom.toMonoidHom (IdeleGroup.infiniteProj wR x)

abbrev xv (v : Pl) (x : IdeleGroup ℚ) : (Qv v)ˣ := IdeleGroup.finiteProj v x

def aR (a : (InfiniteAdeleRing ℚ)ˣ) : ℝˣ :=
  Units.map (eR.toRingHom.comp (Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) wR)).toMonoidHom a

end Ad3.GP
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GaugeC
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel RestrictedProduct

namespace Ad3.GP

def uF (v : Pl) : (𝔸[ℚ])ˣ →* (Qv v)ˣ := Units.map (Reduction.finEval v).toMonoidHom

def uR : (𝔸[ℚ])ˣ →* ℝˣ := Units.map (eR.toRingHom.comp (Reduction.infEval wR)).toMonoidHom

@[simp] theorem coe_uF (v : Pl) (a : (𝔸[ℚ])ˣ) : ((uF v a : (Qv v)ˣ) : Qv v) = (a : 𝔸[ℚ]).2 v := rfl

@[simp] theorem coe_uR (a : (𝔸[ℚ])ˣ) : ((uR a : ℝˣ) : ℝ) = eR ((a : 𝔸[ℚ]).1 wR) := rfl

end Ad3.GP
end
end

