import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifoStatement
section
open NumberField IsDedekindDomain
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summableMajorant_adelicSchwartz_locallyUniform : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {P : Type} [TopologicalSpace P]
    (Ψ : P → (κ → AdeleRing (𝓞 F) F) → ℂ) (p0 : P) (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : P → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ᶠ p in nhds p0, Ψ p = ∑ i, GlobalTheory.WeilM.pureA F (f p i) (g i)) →
    (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C) →
    ∀ x : κ → AdeleRing (𝓞 F) F, ∃ M : (κ → F) → ℝ, Summable M ∧
      ∀ᶠ p in nhds p0, ∀ ξ : κ → F, ‖Ψ p (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ M ξ := by
  first | exact @GlobalTheory.SchwartzMajorant.exists_summable_majorant | exact GlobalTheory.SchwartzMajorant.exists_summable_majorant | (intros; apply GlobalTheory.SchwartzMajorant.exists_summable_majorant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetCharacter

def cut {R : Type} [CommRing R] (ε : R) (h : ε * ε = ε) : R →* R where
  toFun u := (1 - ε) + ε * u
  map_one' := by ring
  map_mul' u v := by linear_combination (-(1 - u - v + u * v)) * h

theorem mul_det_sub_one {R : Type} [CommRing R] {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, a * (M - 1) i j = 0) : a * (M.det - 1) = 0 := by
  let I : Ideal R := LinearMap.ker (LinearMap.mul R R a)
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at h2
  exact Ideal.Quotient.eq.1 h2

theorem cut_eq {R : Type} [CommRing R] {ε e f d : R} (a1 : ε * e = e)
    (a2 : ε * f = 0) (hd : (1 - (e + f)) * (d - 1) = 0) : (1 - ε) + ε * d = e * d + (1 - e) := by
  linear_combination ε * hd + (d - 1) * (a1 + a2)

theorem cut_mul {R : Type} [CommRing R] {ε e f d d' : R} (e2 : f * f = f) (a1 : ε * e = 0)
    (a2 : ε * f = f) (hd : (1 - (e + f)) * (d - 1) = 0) (e3 : d * d' = 1) :
    ((1 - ε) + ε * d) * (f * d' + (1 - f)) = 1 := by
  have e4 : ε * (d - 1) = f * (d - 1) := by
    linear_combination ε * hd + (d - 1) * (a1 + a2)
  linear_combination (1 + f * (d' - 1)) * e4 + (d - 1) * (d' - 1) * e2 + f * e3

variable {D : D7}

theorem det_mul_conj (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det = 1 := by
  have h : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  have hu := (GlobalTheory.LatVac.gram_det_isUnit V).map (incA D)
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply (cA D), ← RingHom.map_det] at h2
  refine hu.mul_left_cancel ?_
  linear_combination h2

theorem algebraMap_norm (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) z) = z * cA D z := by
  have hx : ∃ x, D.sp.cm.sig x ≠ x := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun x => (D.sp.cm.fixed x).1 (h x)
    have h1 : Module.finrank D.host.F D.host.E = 1 := by
      rw [← (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq, Module.finrank_self]
    have h2 := D.sp.cm.deg2
    omega
  obtain ⟨δ, -, h⟩ := GlobalTheory.QuadNormBase.norm_form D.host.F D.host.E D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x) hx
  obtain ⟨x, y, e1, e2⟩ := (h (AF D.host.F)).1 z
  rw [e1, e2]

theorem char_norm {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (x x' : (AE D)ˣ)
    (hx : (x' : AE D) = cA D x) : χ x * χ x' = 1 := by
  obtain ⟨⟨η, hη⟩, h1⟩ := h
  have e : x * x' = idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) := by
    refine Units.ext ?_
    rw [Units.val_mul, hx]
    exact (algebraMap_norm (x : AE D)).symm
  rw [← map_mul, e, h1 η hη, hη.2.2.1 x, one_pow]

theorem char_eq_of_mul_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (y x : (AE D)ˣ)
    (hy : (y : AE D) * cA D x = 1) : χ y = χ x := by
  obtain ⟨x', hx'⟩ : IsUnit (cA D x) := x.isUnit.map (cA D)
  have hc := char_norm h x x' hx'
  have h1 : y * x' = 1 := Units.ext (by rw [Units.val_mul, hx', hy, Units.val_one])
  have h2 := congrArg χ h1
  rw [map_mul, map_one, ← hc] at h2
  exact mul_right_cancel h2

def cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : GA D V →* (AE D)ˣ :=
  (Units.map (cut ε h)).comp ((Matrix.GeneralLinearGroup.det (n := Fin V.rank) (R := AE D)).comp (matHom V))

theorem cutDet_val (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V) :
    (cutDet ε h V g : AE D) = (1 - ε) + ε * (Formalism.L2.Theta.mt V g).det := rfl

theorem cutDet_eq_one (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V)
    (hg : ∀ i j, ε * (Formalism.L2.Theta.mt V g - 1) i j = 0) : cutDet ε h V g = 1 := by
  refine Units.ext ?_
  rw [cutDet_val, Units.val_one]
  linear_combination mul_det_sub_one ε _ hg

theorem continuous_cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : Continuous (cutDet ε h V) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h0 : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  have h1 : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp h0
  have h2 : Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := by
    have e : (fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹) = fun g => ((matHom V g)⁻¹).1 := by
      funext g
      unfold Formalism.L2.Theta.mt
      rw [map_inv]
    rw [e]
    exact Units.continuous_coe_inv.comp h0
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add (continuous_const.mul h1.matrix_det)
  · simp only [← map_inv, cutDet_val]
    exact continuous_const.add (continuous_const.mul h2.matrix_det)

theorem cutDet_real (ε : AE D) (h1 : ε * ε = ε) (h3 : infPart D ε = 0) (V : HSp D) (g : GA D V) (hg : g ∈ GinfC V) :
    cutDet ε h1 V g = 1 := by
  refine cutDet_eq_one ε h1 V g fun i j => ?_
  have hm : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val (show finHom V g = 1 from hg)
  have hf : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
    have e1 : finPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
      congrFun (congrFun hm i) j
    rw [Matrix.sub_apply, RingHom.map_sub, e1, sub_eq_zero]
    by_cases e : i = j
    · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
  exact GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h3, zero_mul, RingHom.map_zero])
    (by rw [RingHom.map_mul, hf, mul_zero, RingHom.map_zero])

theorem det_supp {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (1 - (e + cA D e)) * ((Formalism.L2.Theta.mt V g).det - 1) = 0 :=
  mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]

set_option maxHeartbeats 1000000 in
theorem cutDet_same (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (a1 : ε * e = e) (a2 : ε * cA D e = 0) {V : HSp D} {g : GA D V}
    {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) : cutDet ε h1 V g = x := by
  have hx' : (x : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
  refine Units.ext ?_
  rw [cutDet_val, hx']
  exact cut_eq a1 a2 (det_supp hg)

set_option maxHeartbeats 1000000 in
theorem cutDet_conj (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (he : e * e = e) (a1 : ε * e = 0) (a2 : ε * cA D e = cA D e)
    {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) :
    (cutDet ε h1 V g : AE D) * cA D x = 1 := by
  have hx' : (x : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
  have e2 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have e5 : cA D x = cA D e * cA D (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
    rw [hx', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
  rw [cutDet_val, e5]
  exact cut_mul e2 a1 a2 (det_supp hg) (det_mul_conj V g)

set_option maxHeartbeats 1000000 in

theorem exists_character : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  rintro D ε ⟨h1, -, h3, h4, h5⟩ V χ n hχ hres
  refine ⟨χ.comp (cutDet ε h1 V), hχ.1.comp (continuous_cutDet ε h1 V), fun g hg => ?_, fun v η hv g hg => ?_,
    fun e he g x hg hx => ?_⟩
  · rw [MonoidHom.comp_apply, cutDet_real ε h1 h3 V g hg, map_one]
  · rw [MonoidHom.comp_apply, cutDet_eq_one ε h1 V g fun i j => ?_, map_one]
    rw [← hg i j, ← mul_assoc, mul_comm ε, h5 v η hv, zero_mul]
  · rw [MonoidHom.comp_apply]
    rcases h4 e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rw [cutDet_same ε h1 a1 a2 hg hx]
    · exact char_eq_of_mul_conj hres _ x (cutDet_conj ε h1 he.1 a1 a2 hg hx)

end GlobalTheory.SplitDetCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilChange

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) where
  quasi γ w := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi]
    ring
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul, h u hu h0]⟩
  cont := hf.cont.const_smul c
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).const_smul c

theorem triv_of_resEta_zero {ν : (AE D)ˣ →* Circle} (h : ResEta D ν 0) (a : (AF D.host.F)ˣ) : ν (idF D a) = 1 := by
  obtain ⟨η, hη⟩ := h.1
  rw [h.2 η hη a, pow_zero]

theorem hecke_mul {χ ν : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hν : IsHeckeChar D ν) : IsHeckeChar D (χ * ν) :=
  ⟨hχ.1.mul hν.1, fun x => by rw [MonoidHom.mul_apply, hχ.2, hν.2, mul_one]⟩

theorem hecke_inv {ν : (AE D)ˣ →* Circle} (hν : IsHeckeChar D ν) : IsHeckeChar D ν⁻¹ :=
  ⟨hν.1.inv, fun x => by rw [MonoidHom.inv_apply, hν.2, inv_one]⟩

theorem exists_weilDatum_twist : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (νS νT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 → ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h) := by
  intro D ψ hψ S T χS χT νS νT om ho hS hT rS rT
  obtain ⟨a, aval, amul, anorm, arat, acont⟩ :=
    GlobalTheory.Member.exists_muVal D S νT⁻¹ (hecke_inv hT) (triv_of_resEta_zero (resEta_inv rT))
  obtain ⟨b, bval, bmul, bnorm, brat, bcont⟩ := GlobalTheory.Member.exists_muVal D T νS hS (triv_of_resEta_zero rS)
  have a1 : a 1 = 1 := arat 1 (one_mem _)
  have b1 : b 1 = 1 := brat 1 (one_mem _)
  let om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ) :=
    { toFun := fun p => (a p.1 * b p.2) • om p
      map_one' := by rw [Prod.fst_one, Prod.snd_one, a1, b1, map_one, one_mul, one_smul]
      map_mul' := fun p q => by
        rw [Prod.fst_mul, Prod.snd_mul, amul, bmul, map_mul, smul_mul_smul_comm, mul_mul_mul_comm] }
  have happ : ∀ p f, om' p f = (a p.1 * b p.2) • om p f := fun p f => rfl
  have hval : ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y →
      a g * b h = (((νT x)⁻¹ * νS y : Circle) : ℂ) := by
    intro g h x y hx hy
    rw [aval.2 g x hx, bval.2 h y hy, Circle.coe_mul, MonoidHom.inv_apply]
  refine ⟨om', ⟨hψ, hecke_mul ho.hecS hS, hecke_mul ho.hecT hT, resEta_mul ho.resS rS, resEta_mul ho.resT rT,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p f hf
    rw [happ]
    exact thetaO_smul _ (ho.om_pres p f hf)
  · intro g h w₀ f hf
    rw [happ, happ, heisO_smul, ho.om_heis g h w₀ f hf]
  · intro γ hγ γ' hγ' f hf
    rw [happ, arat γ hγ, brat γ' hγ', one_mul, one_smul]
    exact ho.om_aut γ hγ γ' hγ' f hf
  · intro f hf w
    exact ((acont.comp continuous_fst).mul (bcont.comp continuous_snd)).mul (ho.om_cont f hf w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    rw [← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]
    refine lintegral_congr fun w => ?_
    have hn : ‖om' p f w‖ = ‖om p f w‖ := by
      rw [happ, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, anorm, bnorm, one_mul, one_mul]
    rw [← ofReal_norm, ← ofReal_norm, hn]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := ho.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [happ, map_smul, H ℓ hℓ f hf,
      hval g h x y (isDetAt_root he S g hg x hx) (isDetAt_root he T h hh y hy)]
    simp only [splitFacO, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]
    ring
  · intro g h x y hx hy
    rw [← hval g h x y hx hy]
    rfl

end GlobalTheory.WeilChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPolynomialDegreeLeRank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResDeg

section Poly

variable {K : Type} [Field K]

theorem natDegree_heckePolyOf_le (n q : ℕ) (a : ℕ → K) : (Formalism.L2.Col.heckePolyOf n q a).natDegree ≤ n := by
  unfold Formalism.L2.Col.heckePolyOf
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

theorem linear_eq (a : K) : (1 - C a * X : K[X]) = C (-a) * X + C 1 := by
  rw [C_neg, C_1]; ring

theorem linear_natDegree {a : K} (ha : a ≠ 0) : (1 - C a * X : K[X]).natDegree = 1 := by
  rw [linear_eq]; exact natDegree_linear (neg_ne_zero.2 ha)

theorem linear_ne_zero {a : K} (ha : a ≠ 0) : (1 - C a * X : K[X]) ≠ 0 := by
  intro h
  have := linear_natDegree ha
  rw [h] at this
  simp at this

theorem blockPoly_ne_zero {ν : K} {q : ℕ} (t : ℕ) (hν : ν ≠ 0) (hq : (q : K) ≠ 0) : Formalism.L2.Col.blockPoly ν q t ≠ 0 := by
  unfold Formalism.L2.Col.blockPoly
  exact Finset.prod_ne_zero_iff.2 fun c _ => linear_ne_zero (mul_ne_zero hν (pow_ne_zero _ hq))

theorem blockPoly_natDegree {ν : K} {q : ℕ} (t : ℕ) (hν : ν ≠ 0) (hq : (q : K) ≠ 0) :
    (Formalism.L2.Col.blockPoly ν q t).natDegree = t := by
  unfold Formalism.L2.Col.blockPoly
  rw [natDegree_prod _ _ fun c _ => linear_ne_zero (mul_ne_zero hν (pow_ne_zero _ hq))]
  rw [Finset.sum_congr rfl fun c _ => linear_natDegree (mul_ne_zero hν (pow_ne_zero c hq))]
  simp

theorem blocks_prod {q : ℕ} (t : ℕ) (hq : (q : K) ≠ 0) (l : List K) (hl : ∀ ν ∈ l, ν ≠ 0) :
    (l.map fun ν => Formalism.L2.Col.blockPoly ν q t).prod ≠ 0 ∧
      (l.map fun ν => Formalism.L2.Col.blockPoly ν q t).prod.natDegree = l.length * t := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih fun ν hν => hl ν (by simp [hν])
    have ha : a ≠ 0 := hl a (by simp)
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨mul_ne_zero (blockPoly_ne_zero t ha hq) h1, ?_⟩
    rw [natDegree_mul (blockPoly_ne_zero t ha hq) h1, h2, blockPoly_natDegree t ha hq]
    ring

end Poly

theorem natDegree_res_le {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) {s : ℕ} (hB : B.Ok s) {Xs : Finset (G → K)} {Sg : Pl0 → K[X]} (h : Sg ∈ B.resSet Xs) (P : B.Pl) :
    (Sg (B.pl P)).natDegree ≤ B.n - B.bl.length * B.t := by
  obtain ⟨x, hx, -⟩ := B.lf_exists_occurs_of_mem_resSet h
  by_cases h0 : Sg (B.pl P) = 0
  · simp [h0]
  have hq : ((B.q P : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (hB.q_pos P).ne'
  have hb := blocks_prod B.t hq (B.bl.map fun ν => ν P) (by
    intro a ha
    obtain ⟨ν, hν, rfl⟩ := List.mem_map.1 ha
    exact hB.blocks.ne_zero ν hν P)
  rw [List.map_map, List.length_map] at hb
  have hd : (Formalism.L2.Col.heckePoly B.n B.q x P).natDegree ≤ B.n := natDegree_heckePolyOf_le _ _ _
  have hb1 : B.blockProd P ≠ 0 := hb.1
  have hb2 : (B.blockProd P).natDegree = B.bl.length * B.t := hb.2
  rw [hx P, natDegree_mul h0 hb1, hb2] at hd
  omega

theorem natDegree_polE_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}
    (hA : A.fam.Ok s) (hR : R.Char F) (p : A.fam.base.Ix) (P : Pl0) (hP : P ∈ A.ok A.μ0) :
    (RealDat.polE (A := A) p.1 P).natDegree ≤ D.R.r := by
  obtain ⟨_, _, _, ht⟩ := hR.fam.tie
  have hr : A.r = D.R.r := ht.ranks.2.1
  have h1 := natDegree_res_le (A.fam.R A.fam.μ0) (hA.what₂ _)
    ((A.fam.R A.fam.μ0).lf_mem_resSet_of_mem_ixFin p.2) ⟨P, hP⟩
  have e1 : (A.fam.R A.fam.μ0).n = A.r + D.R.m * A.t := rfl
  have e2 : (A.fam.R A.fam.μ0).bl.length = D.R.m := List.length_ofFn
  have e3 : (A.fam.R A.fam.μ0).t = A.t := rfl
  rw [e1, e2, e3, Nat.add_sub_cancel, hr] at h1
  have h2 : (p.1 P).natDegree ≤ D.R.r := h1
  unfold RealDat.polE
  refine natDegree_comp_le.trans ?_
  calc _ ≤ D.R.r * 1 := Nat.mul_le_mul (natDegree_map_le.trans h2)
        ((natDegree_C_mul_le _ _).trans natDegree_X_le)
    _ = D.R.r := mul_one _

end GlobalTheory.ResDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumEqFinsumConjugacyClassesCentraliserCosets
section
open GlobalTheory.BCT

namespace GlobalTheory.ConjRegroup

theorem finsum_fibres {H C : Type} (p : H → C) (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : C, ∑ᶠ x, Set.indicator {x | p x = c} a x := by
  classical
  have h1 : ∀ c : C, ∑ᶠ x, Set.indicator {x | p x = c} a x
      = ∑ x ∈ ha.toFinset, if c = p x then a x else 0 := by
    intro c
    rw [finsum_eq_sum_of_support_subset (s := ha.toFinset)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      simp [Set.indicator_apply, eq_comm]
    · intro x hx
      have : a x ≠ 0 := fun h => hx (by simp [Set.indicator_apply, h])
      simpa using this
  simp_rw [h1]
  rw [finsum_sum_comm]
  · rw [finsum_eq_sum a ha]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [finsum_eq_single _ (p x)]
    · simp
    · intro c hc
      simp [hc]
  · intro x _
    refine (Set.finite_singleton (p x)).subset ?_
    intro c hc
    by_contra h
    exact hc (if_neg h)

theorem mk_eq_iff {H : Type} [Group H] (x y : H) :
    (Quot.mk _ x : TwCl (MonoidHom.id H)) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * g := by
  have he : Equivalence fun x y : H => ∃ g, y = g⁻¹ * x * (MonoidHom.id H) g := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  exact Quot.eq.trans he.eqvGen_iff

theorem conj_injective {H : Type} [Group H] (r : H) :
    Function.Injective fun δ : H ⧸ twCent (MonoidHom.id H) r =>
      Quotient.out δ * r * (Quotient.out δ)⁻¹ := by
  intro δ ε h
  rw [← QuotientGroup.out_eq' δ, ← QuotientGroup.out_eq' ε, QuotientGroup.eq]
  change (Quotient.out δ)⁻¹ * Quotient.out ε * r = r * ((Quotient.out δ)⁻¹ * Quotient.out ε)
  simp only at h
  calc (Quotient.out δ)⁻¹ * Quotient.out ε * r
      = (Quotient.out δ)⁻¹ * (Quotient.out ε * r * (Quotient.out ε)⁻¹) * Quotient.out ε := by group
    _ = r * ((Quotient.out δ)⁻¹ * Quotient.out ε) := by rw [← h]; group

theorem range_conj {H : Type} [Group H] (c : TwCl (MonoidHom.id H)) :
    Set.range (fun δ : H ⧸ twCent (MonoidHom.id H) c.rep =>
      Quotient.out δ * c.rep * (Quotient.out δ)⁻¹)
      = {x | (Quot.mk _ x : TwCl (MonoidHom.id H)) = c} := by
  have hc : (Quot.mk _ c.rep : TwCl (MonoidHom.id H)) = c := Quot.out_eq c
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨δ, rfl⟩
    refine Eq.trans ?_ hc
    rw [mk_eq_iff]
    exact ⟨Quotient.out δ, by group⟩
  · intro h
    obtain ⟨g, hg⟩ := (mk_eq_iff x c.rep).1 (h.trans hc.symm)
    refine ⟨QuotientGroup.mk g, ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (twCent (MonoidHom.id H) c.rep) g
    have hk2 : (k : H) * c.rep = c.rep * k := k.2
    rw [hk]
    calc g * k * c.rep * (g * k)⁻¹ = g * (k * c.rep) * (g * k)⁻¹ := by group
      _ = g * c.rep * g⁻¹ := by rw [hk2]; group
      _ = x := by rw [hg]; group

theorem finsum_eq_finsum_classes {H : Type} [Group H] (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H), ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
      a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) := by
  rw [finsum_fibres (fun x => (Quot.mk _ x : TwCl (MonoidHom.id H))) a ha]
  refine finsum_congr fun c => ?_
  rw [← finsum_mem_def, ← range_conj c, finsum_mem_range (conj_injective (TwCl.rep c))]

end GlobalTheory.ConjRegroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormNonNormCancelStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussIntegral_normForm_nonNorm_cancel : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (t : Fˣ), t ∉ (Units.map (Algebra.norm F : E →* F)).range → ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → (∫ z in {z : E | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ (Algebra.norm F z) ∂μ) + (nabs F t : ℂ) * ∫ z in {z : E | (t : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((t : F) * Algebra.norm F z) ∂μ = 0 := by
  first | exact @GlobalTheory.KSp.Cancel.gauss_cancel | exact GlobalTheory.KSp.Cancel.gauss_cancel | (intros; apply GlobalTheory.KSp.Cancel.gauss_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOneParaStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ (f f' : VA F N → ℂ) (C : ℝ), Continuous f → Continuous f' → (∀ w, ‖f w‖ ≤ C) → (∀ w, ‖f' w‖ ≤ C) → ∀ M : ℝ →+ VA F N, Continuous M → (∀ w s, HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (heisV ψ (M s) f' w) s) → ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0 := by
  first | exact @GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV | exact GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV | (intros; apply GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV <;> assumption)
end

