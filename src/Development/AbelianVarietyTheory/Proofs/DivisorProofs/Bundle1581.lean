import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0953
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.CountLit

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsOfUnityMapBijectiveOfHenselian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory

theorem rootOfUnity_eq_one_of_map_eq_one {R K : Type} [CommRing R] [IsLocalRing R] [CommRing K]
    [Nontrivial K] (φ : R →+* K) (n : ℕ) (hn : IsUnit (n : R)) (w : R) (hw : w ^ n = 1)
    (hφ : φ w = 1) : w = 1 := by
  have hx : w - 1 ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    have := h.map φ
    rw [map_sub, hφ, map_one, sub_self] at this
    exact not_isUnit_zero this
  have hres : IsLocalRing.residue R w = 1 := by
    rw [← sub_eq_zero, ← map_one (IsLocalRing.residue R), ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hx
  have hS : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one]
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn
    simpa using this
  have h0 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by
    rw [geom_sum_mul, hw, sub_self]
  exact sub_eq_zero.1 (hS.mul_right_eq_zero.1 h0)

theorem units_rootOfUnity_map_injective {R K : Type} [CommRing R] [IsLocalRing R] [CommRing K]
    [Nontrivial K] (φ : R →+* K) (n : ℕ) (hn : IsUnit (n : R)) (u v : Rˣ) (hu : u ^ n = 1)
    (hv : v ^ n = 1) (huv : Units.map φ.toMonoidHom u = Units.map φ.toMonoidHom v) : u = v := by
  have hφ : φ (u : R) = φ (v : R) := by
    have := congrArg (fun x : Kˣ => (x : K)) huv
    simpa using this
  have hw : ((u * v⁻¹ : Rˣ) : R) = 1 := by
    apply rootOfUnity_eq_one_of_map_eq_one φ n hn
    · rw [← Units.val_pow_eq_pow_val, mul_pow, hu, inv_pow, hv, inv_one, _root_.mul_one, Units.val_one]
    · rw [Units.val_mul, map_mul, hφ, ← map_mul, Units.mul_inv, map_one]
  exact mul_inv_eq_one.1 (Units.ext hw)

theorem exists_rootOfUnity_lift {R : Type} [CommRing R] [HenselianLocalRing R] (n : ℕ)
    (hn0 : 0 < n) (hn : IsUnit (n : R)) (z : IsLocalRing.ResidueField R) (hz : z ^ n = 1) :
    ∃ a : R, a ^ n = 1 ∧ IsLocalRing.residue R a = z := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective z
  have hm : (Polynomial.X ^ n - 1 : Polynomial R).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : R) hn0.ne'
  have ha₀ : IsUnit a₀ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hn0.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨a, ha, hd⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ n - 1) hm a₀ (by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp [hz]) (by
      simp [Polynomial.derivative_X_pow]
      exact ⟨hn, ha₀.pow _⟩)
  refine ⟨a, ?_, ?_⟩
  · simpa [sub_eq_zero] using ha
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hd

end GlobalTheory

namespace GlobalTheory

theorem rootsOfUnity_map_bijective_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type) [Field K] (φ : R →+* K) (n : ℕ), 0 < n →
    IsUnit (n : R) →
    (∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → Units.map φ.toMonoidHom u = Units.map φ.toMonoidHom v → u = v) ∧
    ∀ z : Kˣ, z ^ n = 1 → ∃ u : Rˣ, u ^ n = 1 ∧ Units.map φ.toMonoidHom u = z := by
  intro R _ _ _ K _ φ n hn0 hn
  refine ⟨fun u v hu hv huv => units_rootOfUnity_map_injective φ n hn u v hu hv huv, ?_⟩
  haveI : NeZero n := ⟨hn0.ne'⟩
  set ρ := IsLocalRing.residue R
  haveI : NeZero (n : IsLocalRing.ResidueField R) :=
    ⟨by simpa [ρ] using (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn⟩
  let f := restrictRootsOfUnity φ n
  let g := restrictRootsOfUnity ρ n
  have hf : ∀ x : rootsOfUnity n R, ((f x : Kˣ) : K) = φ ((x : Rˣ) : R) := fun x => by
    simp [f]
  have hg : ∀ x : rootsOfUnity n R, ((g x : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R) = ρ ((x : Rˣ) : R) :=
    fun x => by simp [g]
  have ginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply units_rootOfUnity_map_injective ρ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2)
      ((mem_rootsOfUnity _ _).1 y.2)
    apply Units.ext
    have := congrArg (fun w : rootsOfUnity n (IsLocalRing.ResidueField R) => ((w : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)) hxy
    simpa [hg] using this
  have gsurj : Function.Surjective g := by
    intro ζ
    obtain ⟨a, ha, hρ⟩ := exists_rootOfUnity_lift n hn0 hn ((ζ : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)
      (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ζ.2, Units.val_one])
    refine ⟨⟨Units.ofPowEqOne a n ha hn0.ne', (mem_rootsOfUnity _ _).2 (Units.ext (by simp [ha]))⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [hg]
    simpa using hρ
  have hcardR : Nat.card (rootsOfUnity n R) = n := by
    rw [Nat.card_eq_of_bijective g ⟨ginj, gsurj⟩, HasEnoughRootsOfUnity.natCard_rootsOfUnity]
  have finj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply units_rootOfUnity_map_injective φ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2)
      ((mem_rootsOfUnity _ _).1 y.2)
    apply Units.ext
    have := congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hxy
    simpa [hf] using this
  have fbij : Function.Bijective f :=
    finj.bijective_of_nat_card_le (by rw [hcardR]; exact card_rootsOfUnity K n)
  intro z hz
  obtain ⟨x, hx⟩ := fbij.2 ⟨z, (mem_rootsOfUnity _ _).2 hz⟩
  refine ⟨x, (mem_rootsOfUnity _ _).1 x.2, ?_⟩
  apply Units.ext
  have := congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hx
  simpa [hf] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowEigensystemCarriedByFiniteType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Div

theorem span_range_comp_basis {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) :
    Submodule.span ℂ (Set.range fun k => j (b k)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨b k, rfl⟩)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem exists_sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (op : I → Module.End K V)
    (opC : I → Module.End ℂ W) (Z : Submodule K V) (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hcomm : ∀ i v, j (op i v) = opC i (j v))
    (hpc : Formalism.L2.Col.PairComm op) (hso : Formalism.L2.Col.SplitOver op) (x : I → ℂ) (u : W)
    (hu : ∀ i, opC i u = x i • u) (hu0 : u ≠ 0) (huZ : u ∈ Submodule.span ℂ (j '' (Z : Set V))) :
    ∃ s : I → K, x = (fun i => σ (s i)) ∧
      Formalism.L2.Col.eigAt opC x = Submodule.span ℂ (j '' (Formalism.L2.Col.eigAt op s : Set V)) ∧
      ∃ f, f ≠ 0 ∧ f ∈ Z ∧ f ∈ Formalism.L2.Col.eigAt op s := by
  have hsp' : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤ := (span_range_comp_basis σ j b).trans hsp
  have key := GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp' hcomm
  have hmem : u ∈ Formalism.L2.Col.eigAt opC x := Formalism.L2.Col.mem_eigAt_of_forall_apply hu
  have hocc : Formalism.L2.Col.Occurs opC x := fun hbot => hu0 ((Submodule.eq_bot_iff _).1 hbot u hmem)
  obtain ⟨s, _, rfl⟩ := key.2.2 hpc hso x hocc
  refine ⟨s, rfl, (key.1 s).symm, ?_⟩
  have hin : u ∈ Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) := by
    rw [← GlobalTheory.span_image_inf_of_linearIndependent σ j b hli]
    exact ⟨huZ, (key.1 s) ▸ hmem⟩
  by_contra hcon
  push_neg at hcon
  apply hu0
  have hle : Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    by_cases hy0 : y = 0
    · subst hy0; simp
    · exact absurd hy.2 (hcon y hy0 hy.1)
  exact (Submodule.mem_bot ℂ).1 (hle hin)

theorem map_le_span_image {K V W H : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] W) (Θ : H →ₗ[ℂ] W) (E : Submodule ℂ H)
    (A B : Submodule K V) (h : ∀ v ∈ E, Θ v ∈ Submodule.span ℂ (j '' (A : Set V))) (hAB : A ≤ B) :
    E.map Θ ≤ Submodule.span ℂ (j '' (B : Set V)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  exact Submodule.span_mono (Set.image_mono hAB) (h v hv)

set_option maxHeartbeats 400000 in

theorem carries_of_eEc_ne_bot : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → Nonempty A3.fam3.base3.Ix → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hCW hEx hSch hTw hHk hPG hIx c hc
  obtain ⟨Tc, hTc, hx⟩ := GlobalTheory.T.operatorFamily_adjointLift_single_eigensystem R F hLI hOk hCW hEx hSch hTw hHk
  obtain ⟨x, hxc⟩ := hx c
  by_cases h0 : ∀ w ∈ R.EEc c, LinearMap.adjoint (R.Th A3.A.μ0) w = 0
  · obtain ⟨p⟩ := hIx
    refine ⟨p, hc, ?_⟩
    rewrite [Submodule.map_le_iff_le_comap]
    intro w hw
    have h := h0 w hw
    simp only [Submodule.mem_comap, h, Submodule.zero_mem]
  push_neg at h0
  obtain ⟨w, hw, hne⟩ := h0
  let b := (A3.A.fam.R A3.A.μ0).S.basis
  let j := R.jX A3.A.μ0
  let op := (A3.rowI A3.A.μ0).opAll
  have hmodels := hCW.base.models
  have hjX := GlobalTheory.OneFormTest.model_jX R.toRealDat hmodels.HX hmodels.jX A3.A.μ0
  have hExt := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R A3.A.μ0).pres).2.1
  have h2 : ∀ f, (R.HX A3.A.μ0).e (R.jX A3.A.μ0 f) = (R.B.R A3.A.μ0).pres.extL f := hmodels.jX A3.A.μ0
  have hli0 : LinearIndependent ℂ (fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k)) := hExt.1
  have hli : LinearIndependent ℂ (fun k => j (b k)) := by
    refine LinearIndependent.of_comp (R.HX A3.A.μ0).e ?_
    have h3 : ((R.HX A3.A.μ0).e ∘ fun k => j (b k)) =
        fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k) := funext fun k => h2 _
    rewrite [h3]
    exact hli0
  have hcomm : ∀ i f, j (op i f) = Tc i (j f) := hTc
  have hpc : Formalism.L2.Col.PairComm op := (hOk.what₂ A3.A.μ0).comm
  have hso : Formalism.L2.Col.SplitOver op := by
    rintro (i | k)
    · exact (hOk.ok2.what₂ A3.A.μ0).split i
    · exact (hOk.what₂ A3.A.μ0).split k
  have hZ := (GlobalTheory.T.range_adjoint_le_span_jX_image_ZHg R F hLI hOk hCW hEx hSch hPG).1 A3.A.μ0
  obtain ⟨s', hxs, heig, f, hf0, hfZ, hfE⟩ := exists_sys_of_mem_span D.what₂.embLL j b op Tc
    ((A3.A.fam.R A3.A.μ0).ZHg A3.A.X) hli hjX.2.2 hcomm hpc hso x (LinearMap.adjoint (R.Th A3.A.μ0) w) (hxc w hw) hne
    (hZ ⟨w, rfl⟩)
  obtain ⟨p, hp⟩ := GlobalTheory.Div.exists_ix_of_mem_eigAt A3 hOk s' f hf0 hfZ hfE
  refine ⟨p, hc, map_le_span_image j (LinearMap.adjoint (R.Th A3.A.μ0)) (R.EEc c) (Formalism.L2.Col.eigAt op s')
    ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1)
    (fun v hv => heig.le (Formalism.L2.Col.mem_eigAt_of_forall_apply (hxc v hv))) (Formalism.L2.Col.eigAt_le_eigSum hp)⟩

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
section
set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.AllWt GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FlagTan GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

private theorem evR_eq_zero_of_genVal_eq_zero {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) {L : Type} [Field L] [Algebra c.F L] (z : FrPt Xo c L) :
    evR Xo c g z = 0 := by
  obtain ⟨hL, -, hG, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨C, ψ, z0, t', hψ, hb⟩ := hA hG L z
  rw [evR_frBor hg hb]
  have hnat := (mem_secZ.mp hg).1
  obtain ⟨p, φ0, u, hu⟩ := hL.test C.R C.y
  have e1 : evR Xo c g z0 = (ψ.comp φ0) (g p u) :=
    evR_eq hnat (frMap_comp (χ := ψ.comp φ0) hu hψ (fun _ => rfl))
  have e2 : evR Xo c g C.yg = (C.R.val.comp φ0) (g p u) :=
    evR_eq hnat (frMap_comp (χ := C.R.val.comp φ0) hu C.gen (fun _ => rfl))
  have e3 := evR_frBor hg C.bor
  have e4 : evR Xo c g (genFr hG C.Z) = 0 := by
    have h1 := h0 C.Z
    rw [genVal_apply hG] at h1
    exact h1
  rw [e4, mul_zero, e2, AlgHom.comp_apply, Subalgebra.coe_val] at e3
  have e5 : φ0 (g p u) = 0 := Subtype.ext e3
  rw [e1, AlgHom.comp_apply, e5, map_zero, mul_zero]

theorem secZ_eq_zero_of_genVal {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) : g = 0 :=by
  funext p u
  obtain ⟨a, ha⟩ : ∃ a, Ideal.Quotient.mk p.I a = g p u := Ideal.Quotient.mk_surjective _
  show g p u = 0
  rw [← ha, Ideal.Quotient.eq_zero_iff_mem]
  have hJ : p.I.jacobson = p.I := by
    first
    | exact IsJacobsonRing.out' _ p.rad
    | exact IsJacobsonRing.out inferInstance p.rad
    | exact Ideal.IsJacobson.out' _ p.rad
  rw [← hJ, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hIm, hm⟩
  letI : Field (MvPolynomial _ c.F ⧸ m) := Ideal.Quotient.field m
  let φ : p.R →ₐ[c.F] MvPolynomial _ c.F ⧸ m := Ideal.Quotient.factorₐ c.F hIm
  obtain ⟨z, hz⟩ := exists_frMap φ u
  have h1 := evR_eq (mem_secZ.mp hg).1 hz
  rw [evR_eq_zero_of_genVal_eq_zero hg h0 z, ← ha] at h1
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h1.symm

theorem genVal_eq_zero_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Z : Comp Xo c) (e : Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, genVal Z f = 0 ↔ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c f y = 0 :=by
  intro E _ _ _ H Dw l Xo c Z e f hf
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  constructor
  · intro h0 S _ _ y hy
    by_cases ht : Tested y
    · have hz : idem Z * f = 0 := by
        refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hf) (fun Z' => ?_)
        by_cases hZ : Z' = Z
        · subst hZ
          rw [map_mul, h0, mul_zero]
        · rw [genVal_apply hG]
          exact evC_eq_zero hG hZ (mul_comm f (idem Z) ▸ mul_mem_suppOn f (idem_mem_suppOn Z))
      have h1 : evR Xo c (idem Z * f) y = evR Xo c (idem Z) y * evR Xo c f y := evalAt_mul _ _ _ _ y
      rw [hz, evR_idem hy ht, one_mul] at h1
      rw [← h1]
      exact evalAt_zero _ _ y
    · unfold evR evalAt
      rw [dif_neg ht]
  · intro hall
    rw [genVal_apply hG]
    exact hall _ _ (liesOn_genFr hG Z)

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsOfPulledBackLineBundlesOnFrames
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

namespace GlobalTheory.FlagPlucker

theorem det_mul_eq_sum_fun {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det :=
  _root_.GlobalTheory.DeterminantProductExpansion.main A B

theorem exists_sum_minors_eq_one {R : Type} [CommRing R] {n k d : ℕ} (hd : d ≤ k) (A : Matrix (Fin n) (Fin k) R)
    (B : Matrix (Fin k) (Fin n) R) (hBA : B * A = 1) :
    ∃ c : (Fin d → Fin n) → R, ∑ r, c r * (A.submatrix r (Fin.castLE hd)).det = 1 := by
  have e : B.submatrix (Fin.castLE hd) id * A.submatrix id (Fin.castLE hd) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hBA,
      Matrix.submatrix_one _ (Fin.castLE_injective _)]
  refine ⟨fun r => ∏ a, B (Fin.castLE hd a) (r a), ?_⟩
  have := congrArg Matrix.det e
  rw [det_mul_eq_sum_fun, Matrix.det_one] at this
  exact this

end GlobalTheory.FlagPlucker

noncomputable section
namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem exists_mul_plkU_eq_one (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) :
    ∃ B : Matrix (Fin (Dw.mult σ)) (Fin Mc.n) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U), B * plkU F Mc k σ = 1 := by
  obtain ⟨w, hw⟩ := F.split k σ
  have hm : ∀ (M M' : MChart Y) (hle : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ (M.U ⊓ M'.U)) (S : Type) [CommRing S]
      (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)),
      ((chg M M').map (π.appLE _ _ hle).hom).map (ev z _ hz) =
        (chg M M').map (ev (z ≫ π) _ (le_preimage_map π hle hz)) := by
    intro M M' hle S _ z hz
    rw [Matrix.map_map]
    ext a b
    exact ev_appLE z π hle hz _ _
  have hle1 : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ ((F.M k).U ⊓ Mc.U) := fun _ hp => ⟨F.le k hp.1, hp.2⟩
  have hle2 : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ (Mc.U ⊓ (F.M k).U) := fun _ hp => ⟨hp.2, F.le k hp.1⟩
  have hC : (chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom *
      (chg Mc (F.M k).toMChart).map (π.appLE _ _ hle2).hom = 1 := by
    ext i j
    refine ext_ev fun S _ z hz => ?_
    have e : (((chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom *
        (chg Mc (F.M k).toMChart).map (π.appLE _ _ hle2).hom)).map (ev z _ hz) =
        (1 : Matrix (Fin (F.M k).n) (Fin (F.M k).n) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U)).map (ev z _ hz) := by
      have hx := le_preimage_map π hle1 hz
      have hx' := le_preimage_map π hle2 hz
      rw [Matrix.map_mul, hm _ _ hle1, hm _ _ hle2,
        chg_map _ _ (z ≫ π) (le_preimage_mono inf_le_left hx) (le_preimage_mono inf_le_right hx),
        chg_map _ _ (z ≫ π) (le_preimage_mono inf_le_left hx') (le_preimage_mono inf_le_right hx'),
        Module.Basis.toMatrix_mul_toMatrix,
        Module.Basis.toMatrix_self, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrFun (congrFun e i) j
  refine ⟨(w.map (resG Z (inf_le_left : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ F.U k))) *
    (chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom, ?_⟩
  unfold plkU
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((chg (F.M k).toMChart Mc).map _), hC, Matrix.one_mul,
    ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_mem_basicOpen_plkMinor (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ)
    (m : Fin (Dw.mult σ)) (z : Z) (hz : z ∈ F.U k ⊓ π ⁻¹ᵁ Mc.U) :
    ∃ r, z ∈ Z.basicOpen (plkMinor F Mc k σ m r) := by
  obtain ⟨B, hB⟩ := exists_mul_plkU_eq_one F Mc k σ
  obtain ⟨cf, hc⟩ := exists_sum_minors_eq_one (d := (m : ℕ) + 1) m.2 _ B hB
  by_contra hno
  push_neg at hno
  have hmax : (Z.presheaf.germ _ z hz).hom (∑ r, cf r * plkMinor F Mc k σ m r) ∈
      IsLocalRing.maximalIdeal (Z.presheaf.stalk z) := by
    rw [map_sum]
    refine Ideal.sum_mem _ fun r _ => ?_
    rw [map_mul]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => hno r ?_)
    exact (Scheme.mem_basicOpen Z _ z hz).2 hu
  have h1 : ∑ r, cf r * plkMinor F Mc k σ m r = 1 := hc
  rw [h1, map_one] at hmax
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hmax)

end GlobalTheory.FlagPlucker
end

noncomputable section
namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj

theorem iSup_nonzeroLocus_plk : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (t : Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ q, (t q).f = plkLoc F Mc g hg σ m q) → ⨆ q, nonzeroLocus (t q) = ⊤ := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F Mc T g hg σ m t ht
  refine eq_top_iff.2 fun p _ => ?_
  obtain ⟨k, hk⟩ : ∃ k, g.base p ∈ F.U k := by
    have : g.base p ∈ (⨆ k, F.U k) := by rw [F.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hpM : g.base p ∈ π ⁻¹ᵁ Mc.U := by
    have := hg (show p ∈ (⊤ : T.Opens) from trivial)
    simpa using this
  obtain ⟨r, hr⟩ := exists_mem_basicOpen_plkMinor F Mc k σ m (g.base p) ⟨hk, hpM⟩
  let j : ((F.LL (ind σ m)).pull g).ι := fun _ => k
  have hpj : p ∈ ((F.LL (ind σ m)).pull g).U j := mem_pull.2 hk
  let q : Fin (plkNum Mc m + 1) := Fin.succ (Fintype.equivFin _ r)
  have hq : plkIdx Mc m q = some r := by simp [q, plkIdx]
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨q, (mem_nonzeroLocus_iff_basicOpen (t q) hpj).2 ?_⟩
  rw [congrFun (ht q) j]
  unfold plkLoc
  split
  · rename_i h; rw [hq] at h; exact absurd h (by simp)
  · rename_i r' h
    rw [hq] at h
    cases h
    rw [Scheme.basicOpen_appLE]
    exact ⟨hpj, hr⟩

end GlobalTheory.FlagPlucker
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundPeriodicSchwartzStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_bound_periodic_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ (P : ℕ) (C : ℝ) (c : ℕ), ∀ m : ℕ, 0 < m → ∀ f ∈ schA F κ, Per F m f → ∀ b : ℝ, 0 ≤ b → (∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ P → (∀ v ∈ w, ‖v‖ ≤ 1) → ∫⁻ x, ‖wordD F w f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b) → ∀ x, ‖f x‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  first | exact @GlobalTheory.ArchDecay.sobolev_per | exact GlobalTheory.ArchDecay.sobolev_per | (intros; apply GlobalTheory.ArchDecay.sobolev_per <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevUniformBoundPeriodicStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_uniform_bound_periodic : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (ℓ a : ℕ) (C : ℝ), ∀ Ψ ∈ schA F κ, ∀ m : ℕ, 1 ≤ m → (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → Ψ (x + (m : AF F) • a') = Ψ x) → ∀ B : ℝ, 0 ≤ B → (∀ l : List ((κ → AF F) × (κ → AF F)), l.length ≤ ℓ → (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH ψ l Ψ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B) → ∀ x : κ → AF F, ‖Ψ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ C * (m : ℝ) ^ a * (1 + B) := by
  first | exact @GlobalTheory.SobClass.sob_class | exact GlobalTheory.SobClass.sob_class | (intros; apply GlobalTheory.SobClass.sob_class <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassCountTorusDecomposition
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.BCT.FacCl.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → ∃ (ι : Type) (_ : Fintype ι) (K L : ι → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, Field (L i)) (_ : ∀ i, NumberField (L i)) (_ : ∀ i, Algebra (K i) (L i)) (_ : ∀ i, Algebra.IsQuadraticExtension (K i) (L i)) (x : ∀ i, GlobalTheory.QuadSymbol.FinFam (K i)), Fintype.card ι = nfac P ∧ (∀ i, NumberField.IsTotallyReal (K i)) ∧ (∀ i, NumberField.IsTotallyComplex (L i)) ∧ (∀ i, GlobalTheory.QuadSymbol.AlmostNorm (K i) (L i) (x i)) ∧ ∑ i, Fintype.card (InfinitePlace (K i)) = n * Fintype.card (InfinitePlace E) ∧ Nonempty ({c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} ≃ ∀ i, {q : (K i)ˣ ⧸ GlobalTheory.QuadSymbol.globalNorms (K i) (L i) // ∃ t : (K i)ˣ, q = QuotientGroup.mk t ∧ ∀ u, x i u / GlobalTheory.QuadSymbol.finDiag (K i) t u ∈ GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.adicCompletion (K i))}) :=
  CompanionTheory.Rg.BcB.G3.param_lit
end

