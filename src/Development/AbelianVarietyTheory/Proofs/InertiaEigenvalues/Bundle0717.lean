import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0708
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRelationsExtendToPlaceCommonEigen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

variable {D : D7}

theorem psi_ne_zero' (ψ : AddChar (AF D.host.F) ℂ) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem heisO_injective (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) {f g : WO S T → ℂ}
    (h : heisO ψ S T w f = heisO ψ S T w g) : f = g := by
  funext x
  have := congrFun h (x - w)
  simp only [heisO, sub_add_cancel] at this
  exact mul_left_cancel₀ (psi_ne_zero' ψ _) this

theorem heisO_fun_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    heisO ψ S T w (0 : WO S T → ℂ) = 0 := by
  funext x
  simp [heisO]

theorem comb_eq_linearCombination (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ)
    (X : WO S T → ℂ) : comb ψ S T c X = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u X) c := by
  rw [Finsupp.linearCombination_apply]
  rfl

theorem comb_sum_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ι : Type} (s : Finset ι) (r : ι → WO S T)
    (z : ι → ℂ) (X : WO S T → ℂ) :
    comb ψ S T (∑ i ∈ s, Finsupp.single (r i) (z i)) X = ∑ i ∈ s, z i • heisO ψ S T (r i) X := by
  rw [comb_eq_linearCombination, map_sum]
  simp only [Finsupp.linearCombination_single]

theorem comb_fun_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) :
    comb ψ S T c (0 : WO S T → ℂ) = 0 := by
  unfold comb Finsupp.sum
  exact Finset.sum_eq_zero fun u _ => by
    show c u • heisO ψ S T u 0 = 0
    rw [heisO_fun_zero, smul_zero]

theorem relOff_factor {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Sb : Finset (FinPl D)} {p f : WO S T → ℂ}
    (hR : RelOff ψ S T Sb p f) (w : WO S T) (s : Finset (WO S T)) (a e : WO S T → ℂ) (r : WO S T → WO S T)
    (hr : ∀ u ∈ s, OffPl Sb (r u))
    (hp : ∀ u ∈ s, heisO ψ S T u p = e u • heisO ψ S T w (heisO ψ S T (r u) p))
    (hf : ∀ u ∈ s, heisO ψ S T u f = e u • heisO ψ S T w (heisO ψ S T (r u) f))
    (h0 : ∑ u ∈ s, a u • heisO ψ S T u p = 0) : ∑ u ∈ s, a u • heisO ψ S T u f = 0 := by
  classical
  set c' : WO S T →₀ ℂ := ∑ u ∈ s, Finsupp.single (r u) (a u * e u) with hc'
  have key : ∀ X : WO S T → ℂ, (∀ u ∈ s, heisO ψ S T u X = e u • heisO ψ S T w (heisO ψ S T (r u) X)) →
      ∑ u ∈ s, a u • heisO ψ S T u X = heisO ψ S T w (comb ψ S T c' X) := by
    intro X hX
    rw [hc', comb_sum_single, GlobalTheory.SplitScalar.heisO_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hX u hu, GlobalTheory.SplitScalar.heisO_smul, smul_smul]
  have hsupp : ∀ u ∈ c'.support, OffPl Sb u := by
    intro u hu
    obtain ⟨x, hx, hx'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hu)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx')]
    exact hr x hx
  have hp0 : comb ψ S T c' p = 0 := by
    apply heisO_injective ψ S T w
    rw [← key p hp, h0, heisO_fun_zero]
  rw [key f hf, hR c' hsupp hp0, heisO_fun_zero]

theorem offPl_zero (Sb : Finset (FinPl D)) (S T : HSp D) : OffPl Sb (0 : WO S T) :=
  ⟨by ext i j; simp, fun _ _ _ _ _ _ => by simp⟩

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (z : ℂ) (X : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u z) X = z • heisO ψ S T u X := by
  unfold comb
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem isHalf_one_sub {S T : HSp D} {b : AE D} (hb2 : b * b = b) (u : WO S T) : IsHalf (1 - b) (u - b • u) := by
  intro i j
  show (1 - b) * (u i j - b * u i j) = u i j - b * u i j
  rw [mul_sub, sub_mul, sub_mul, one_mul, one_mul, ← mul_assoc, hb2, sub_self, sub_zero]

theorem heisO_decomp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {b : AE D} (hb2 : b * b = b) (hcb : cA D b = b)
    (u u0 : WO S T) (X : WO S T → ℂ) (z : ℂ) (hX : heisO ψ S T (b • u - b • u0) X = z • X) :
    heisO ψ S T u X = ((ψ (symplOH S T (b • u0) (u - b • u0)))⁻¹ * z) •
      heisO ψ S T (b • u0) (heisO ψ S T (u - b • u) X) := by
  have hab : cA D (1 - b) * b = 0 := by rw [map_sub, map_one, hcb, sub_mul, one_mul, hb2, sub_self]
  have horth0 : symplO S T (u - b • u) (b • u - b • u0) = 0 :=
    GlobalTheory.SplitScalar.symplO_eq_zero S T hab (isHalf_one_sub hb2 u)
      (GlobalTheory.SplitScalar.isHalf_sub (GlobalTheory.SplitScalar.isHalf_smul hb2 u) (GlobalTheory.SplitScalar.isHalf_smul hb2 u0))
  have h1 : heisO ψ S T (b • u0) (heisO ψ S T (u - b • u) (heisO ψ S T (b • u - b • u0) X)) =
      ψ (symplOH S T (b • u0) (u - b • u0)) • heisO ψ S T u X := by
    rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T horth0, GlobalTheory.SplitScalar.heisO_heisO, sub_add_sub_cancel,
      add_sub_cancel]
  rw [hX, GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_smul] at h1
  rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (psi_ne_zero' ψ _), one_smul]

theorem offPl_sub_idem {S T : HSp D} {Sb : Finset (FinPl D)} {v : FinPl D} {u : WO S T}
    (hu : OffPl (dropPl Sb v) u) : OffPl Sb (u - idem D (.inl v) • u) := by
  classical
  obtain ⟨hidem, horth, -, hfin, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  refine ⟨Matrix.ext fun i j => ?_, fun q hq ε hε i j => ?_⟩
  · have h : infPart D (u i j) = 0 := congrFun (congrFun hu.1 i) j
    show infPart D (u i j - idem D (.inl v) * u i j) = 0
    rw [map_sub, map_mul, (hfin v).1, h, zero_mul, sub_zero]
  · rw [placeIdem_eq hε]
    show idem D (.inl q) * (u i j - idem D (.inl v) * u i j) = 0
    by_cases hqv : q = v
    · rw [hqv, mul_sub, ← mul_assoc, hidem, sub_self]
    · have hq' : q ∈ dropPl Sb v := by unfold dropPl; exact Finset.mem_erase.2 ⟨hqv, hq⟩
      have h1 := hu.2 q hq' _ ((hfin q).2.2) i j
      rw [placeIdem_eq ((hfin q).2.2)] at h1
      rw [mul_sub, h1, ← mul_assoc, horth (.inl q) (.inl v) (fun h => hqv (Sum.inl.inj h)), zero_mul, sub_zero]

theorem relOff_dropPl_of_coEig : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D))
    (v : FinPl D), v ∈ Sb → ∀ (p f : WO S T → ℂ), (∀ u, IsHalf (idem D (.inl v)) u → CoEig ψ S T p f u ∨
      ∃ l, IsHalf (idem D (.inl v)) l ∧ CoEig ψ S T p f l ∧ ψ (symplO S T l u) ≠ 1) →
    RelOff ψ S T Sb p f → RelOff ψ S T (dropPl Sb v) p f := by
  classical
  intro D ψ S T Sb v _ p f hH hR c hc hcp
  have hrest : ∀ u : WO S T, OffPl (dropPl Sb v) u → OffPl Sb (u - idem D (.inl v) • u) :=
    fun u hu => offPl_sub_idem hu
  obtain ⟨hidem, -, hconj, -, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  obtain ⟨b, hb⟩ : ∃ b, b = idem D (.inl v) := ⟨_, rfl⟩
  rw [← hb] at hH hrest
  have hb2 : b * b = b := by rw [hb]; exact hidem _
  have hcb : cA D b = b := by rw [hb]; exact hconj _
  by_cases hp0 : p = 0
  · have hf0 : f = 0 := by
      have h1 := hR (Finsupp.single 0 1) (fun u hu => by
        rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]; exact offPl_zero Sb S T) (by
        rw [comb_single, GlobalTheory.SplitScalar.heisO_zero, one_smul, hp0])
      rwa [comb_single, GlobalTheory.SplitScalar.heisO_zero, one_smul] at h1
    rw [hf0, comb_fun_zero]

  have hcl : ∀ l : {l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l}, ∃ z : ℂ, z ≠ 0 ∧
      heisO ψ S T l.1 p = z • p ∧ heisO ψ S T l.1 f = z • f := by
    rintro ⟨l, -, z, h1, h2⟩
    refine ⟨z, fun hz => hp0 ?_, h1, h2⟩
    apply heisO_injective ψ S T l
    rw [h1, hz, zero_smul, heisO_fun_zero]
  choose cl hcl0 hclp _ using hcl
  obtain ⟨χ, hχ⟩ : ∃ χ : WO S T → {l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l} → ℂ,
      ∀ u l, χ u l = ψ (symplO S T l.1 u) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : (WO S T → ℂ) → ({l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l} → ℂ) → (WO S T → ℂ),
      ∀ X k, V X k = ∑ u ∈ c.support with χ u = k, c u • heisO ψ S T u X := ⟨_, fun _ _ => rfl⟩
  have hcomb : ∀ X, ∑ k ∈ c.support.image χ, V X k = comb ψ S T c X := by
    intro X
    simp only [hV]
    exact Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_image_of_mem χ hu) _
  have heig : ∀ k ∈ c.support.image χ, ∀ l, GlobalTheory.SplitScalar.heisL ψ S T l.1 (V p k) = (k l * cl l) • V p k := by
    intro k _ l
    rw [GlobalTheory.SplitScalar.heisL_apply, hV, GlobalTheory.SplitScalar.heisO_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← (Finset.mem_filter.1 hu).2, hχ, GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_comm, hclp,
      GlobalTheory.SplitScalar.heisO_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hVp : ∀ k ∈ c.support.image χ, V p k = 0 :=
    GlobalTheory.joint_eigenvectors_eq_zero_of_sum_eq_zero _ _ _ (fun l => GlobalTheory.SplitScalar.heisL ψ S T l.1)
      (fun k l => k l * cl l) (V p) _ heig
      (fun k1 _ k2 _ h => funext fun l => mul_right_cancel₀ (hcl0 l) (congrFun h l)) (by rw [hcomb]; exact hcp)
  have hVf : ∀ k ∈ c.support.image χ, V f k = 0 := by
    intro k hk
    obtain ⟨u0, _, hu0k⟩ := Finset.mem_image.1 hk
    have hCo : ∀ u ∈ c.support.filter (fun u => χ u = k), ∃ z : ℂ,
        heisO ψ S T (b • u - b • u0) p = z • p ∧ heisO ψ S T (b • u - b • u0) f = z • f := by
      intro u hu
      have hχu := (Finset.mem_filter.1 hu).2
      rcases hH _ (GlobalTheory.SplitScalar.isHalf_sub (GlobalTheory.SplitScalar.isHalf_smul hb2 u)
          (GlobalTheory.SplitScalar.isHalf_smul hb2 u0)) with h | ⟨l, hl, hlco, hne⟩
      · exact h
      · exfalso
        apply hne
        have e1 : ψ (symplO S T l u) = ψ (symplO S T l u0) := by
          have := congrFun (hχu.trans hu0k.symm) ⟨l, hl, hlco⟩
          rwa [hχ, hχ] at this
        have hbl : ∀ x, symplO S T l (b • x) = symplO S T l x := fun x => by
          conv_lhs => rw [← hcb]
          rw [← GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.SplitScalar.isHalf_iff _ l).1 hl]
        have e2 : symplO S T l (b • u - b • u0) + symplO S T l (b • u0) = symplO S T l (b • u) := by
          rw [← GlobalTheory.LatVac.symplO_add_right, sub_add_cancel]
        rw [hbl, hbl] at e2
        have e3 := congrArg ψ e2
        rw [AddChar.map_add_eq_mul, e1] at e3
        exact mul_right_cancel₀ (psi_ne_zero' ψ _) (e3.trans (one_mul _).symm)
    choose! eco hecp hecf using hCo
    have key := relOff_factor hR (b • u0) (c.support.filter fun u => χ u = k) c
      (fun u => (ψ (symplOH S T (b • u0) (u - b • u0)))⁻¹ * eco u) (fun u => u - b • u)
      (fun u hu => hrest u (hc u (Finset.mem_filter.1 hu).1))
      (fun u hu => heisO_decomp ψ S T hb2 hcb u u0 p _ (hecp u hu))
      (fun u hu => heisO_decomp ψ S T hb2 hcb u u0 f _ (hecf u hu))
      (by rw [← hV]; exact hVp k hk)
    rw [hV]
    exact key
  rw [← hcomb f]
  exact Finset.sum_eq_zero hVf

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerNeSpherical
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

theorem scalar_of_eigen {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (P : Submodule ℂ H)
    (Wop : H →L[ℂ] H) (hinj : Function.Injective Wop) (heig : ∀ y ∈ P, ∃ z : ℂ, Wop y = z • y) :
    ∃ l : ℂ, l ≠ 0 ∧ ∀ x ∈ P, Wop x = l • x := by
  by_cases h : ∃ x0 ∈ P, x0 ≠ 0
  · obtain ⟨x0, hx0, hne⟩ := h
    obtain ⟨l, hl⟩ := heig x0 hx0
    refine ⟨l, ?_, ?_⟩
    · rintro rfl
      apply hne
      apply hinj
      rw [hl, zero_smul, map_zero]
    · intro x hx
      obtain ⟨lx, hlx⟩ := heig x hx
      obtain ⟨m, hm⟩ := heig (x + x0) (P.add_mem hx hx0)
      rw [map_add, hlx, hl, smul_add] at hm
      by_cases hmx : m = lx
      · subst hmx
        have : (l - m) • x0 = 0 := by
          rw [sub_smul]; exact sub_eq_zero.2 (add_left_cancel hm)
        rcases smul_eq_zero.1 this with h1 | h1
        · rw [hlx, sub_eq_zero.1 h1]
        · exact absurd h1 hne
      · have hx' : x = ((l - m) / (m - lx)) • x0 := by
          have e1 : (m - lx) • x = (l - m) • x0 := by
            rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add]
            rw [← hm]; abel
          have hne' : m - lx ≠ 0 := sub_ne_zero.2 hmx
          rw [div_eq_mul_inv, mul_comm, mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hne', one_smul]
        rw [hx', map_smul, hl, smul_comm]
  · push_neg at h
    refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    rw [h x hx, map_zero, smul_zero]

set_option maxHeartbeats 4000000 in
theorem innerNe_main {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hL : Laws R F) (i : Fin D.R.m) (t : T) (hFS : FinSum R i t) (hFM : FinMult R i t) (hLF : LevFix R i t)
    (hVN : VecNe R i t) (hLS : LocSmall R i t) (hBS : BadSupp R i t) (hLP : LevProd R i) (hTL : TransLaws R i) :
    InnerNe R i t ∅ := by
  intro th hth c
  have hcov := @GlobalTheory.T.exists_covolumeOne_measure_homSpace_of_laws D G _ _ Pl0 T A Ks _ _ _ R F hL i
  obtain ⟨μ, 𝓕, hμ⟩ := hcov
  have hleft := @GlobalTheory.T.fixedVectorCoefficient_left_invariant_levelGroup D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF μ 𝓕 hμ
  have hfa := @GlobalTheory.T.hasSum_innerProduct_finsupp_localCosetFamilies D G _ _ Pl0 T A Ks _ _ _ R i t hLP hTL hFM hLF hVN hFS th hth μ 𝓕 hμ
  have hsm := @GlobalTheory.T.localCoefficient_nontrivialCosets_summable_bound D G _ _ Pl0 T A Ks _ _ _ R i t hLS μ 𝓕 hμ
  obtain ⟨a, ha, hfam⟩ := hfa
  obtain ⟨s, hs, hs1, hsC⟩ := hsm
  have hconv := @GlobalTheory.T.rightTranslateOperator_mul_localOperator_hasSum D G _ _ Pl0 T A Ks _ _ _ R i t hLS hTL hLF μ 𝓕 hμ hleft
  have hupd := @GlobalTheory.T.rightTranslateOperator_familyProd_update D G _ _ Pl0 T A Ks _ _ _ R i hTL
  have heig := @GlobalTheory.T.localOperator_scalar_on_sphericalEigenspace D G _ _ Pl0 T A Ks _ _ _ R F hL i t hBS hLF hLS hLP hTL μ 𝓕 hμ hleft c
  have hUpd : ∀ v (f : ∀ v, Eu.LX R i v), {w | f w ≠ Eu.lx0 R i w}.Finite → f v = Eu.lx0 R i v →
      HasSum (fun x => Eu.acoef R i t μ 𝓕 v x • Eu.Bfam R i (Function.update f v x))
        (Eu.Bfam R i f * Eu.Zop R i t μ 𝓕 v) := by
    intro v f hf hv
    obtain ⟨hG, hB⟩ := hupd f hf v hv
    have := hconv v _ hG
    unfold Eu.Bfam
    simp only [hB]
    exact this
  have hEu := GlobalTheory.T.eulerOperator_injective_eigenvector (HeightOneSpectrum (𝓞 D.host.F)) (Eu.LX R i) (Eu.lx0 R i)
    (R.HW i (sg0 D A)).H (Eu.acoef R i t μ 𝓕) s (Eu.Bfam R i) (Eu.Zop R i t μ 𝓕)
    (local_coefficient_trivial_level_coset hLF hVN hμ) hs hs1 hsC (fun f => bop_norm R i _)
    (by unfold Eu.Bfam; rw [localCosetFamilyRepresentativeProd_trivial_eq_one]; exact bop_one hTL) hUpd
  obtain ⟨Wop, hW, hinj, hWe⟩ := hEu
  have hip : ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = (a : ℂ) * ⟪x, Wop y⟫_ℂ := by
    intro x y
    let φ : ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H) →L[ℂ] ℂ :=
      (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ _ y)
    have h1 := (hW.mapL φ).mul_left (a : ℂ)
    have h2 := hfam x y
    refine h2.unique ?_
    simpa [φ, inner_smul_right] using h1
  have hE : ∀ y ∈ part R i ∅ c, ∃ z : ℂ, Wop y = z • y := by
    intro y hy
    have hz := fun v => heig y hy v
    choose z hz using hz
    exact ⟨_, hWe y z hz⟩
  have hsc := scalar_of_eigen (part R i ∅ c) Wop hinj hE
  obtain ⟨l, hl, hlx⟩ := hsc
  refine ⟨(a : ℂ) * (starRingEnd ℂ) l, mul_ne_zero (by exact_mod_cast ha.ne') (by simpa using hl), ?_⟩
  intro x hx y
  rw [← inner_conj_symm, hip y x, hlx x hx, inner_smul_right, map_mul, map_mul, Complex.conj_ofReal,
    inner_conj_symm]
  ring

end GlobalTheory.RawLift.Eu

namespace GlobalTheory.RawLift

theorem innerNe_spherical : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FinSum R i t → FinMult R i t → LevFix R i t → VecNe R i t → LocSmall R i t → BadSupp R i t → LevProd R i → TransLaws R i → InnerNe R i t ∅ :=
  fun _ _ _ _ _ _ _ _ _ _ _ R F hL _ i t hFS hFM hLF hVN hLS hBS hLP hTL =>
    Eu.innerNe_main R F hL i t hFS hFM hLF hVN hLS hBS hLP hTL

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPlaceModel_comp_restrictToHalfLatticeIndicator : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}, a' * a' = a' → b * b = b → a' * b = 0 → (∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 f₀ (T₀ ∘ₗ restrictHalf a' b Λ) := by
  first | exact @GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf | exact GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf | (intros; apply GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompTensorHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TwoStepModel

variable {D : D7} {m n : ℕ}

def tensorHalf (a' b : AE D) (Ψ : Mx D m n → ℂ) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensorHalf_apply (a' b : AE D) (Ψ Φ : Mx D m n → ℂ) (x : Mx D m n) :
    tensorHalf a' b Ψ Φ x = Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0) := rfl

open GlobalTheory.ExportSeries.RestrictHalfModel

theorem tensorHalf_halfInd (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) (Ψ : Mx D m n → ℂ) :
    tensorHalf a' b Ψ ((1 : ℂ) • halfInd a' Λ) = restrictHalf b a' Λ Ψ := by
  funext x
  simp only [tensorHalf_apply, restrictHalf_apply, one_smul, add_comm b a']
  ring

theorem isSBHalf_tensorHalf {a' b : AE D} (ha' : a' * a' = a') (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Φ Ψ : Mx D m n → ℂ} (hΦ : IsSBHalf a' Λ Φ)
    (hΨ : IsSBHalf b Λ Ψ) : IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  obtain ⟨-, k', hk', hinv', hlat'⟩ := hΨ
  refine ⟨fun t ht => ?_, k * k', Nat.mul_pos hk hk', fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [tensorHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [tensorHalf_apply]
    have e1 : a' • (t + (k * k') • u) = a' • t + k • (a' • (k' • u)) := by
      rw [smul_add, mul_comm k k', mul_smul, smul_comm k' k u, smul_comm a' k]
    have e2 : b • (t + (k * k') • u) = b • t + k' • (b • (k • u)) := by
      rw [smul_add, mul_smul, smul_comm k k' u, smul_comm b k']
    have e3 : (a' + b) • ((k * k') • u) = (k * k') • u := by rw [smul_comm, hhu]
    rw [e1, hinv _ (hΛ a' ha' _ (Λ.nsmul_mem hu k')) (isHalf_smul ha' _), e2,
      hinv' _ (hΛ b hb _ (Λ.nsmul_mem hu k)) (isHalf_smul hb _), isHalf_add_iff e3]
  · rw [tensorHalf_apply] at ht
    have h1 : Φ (a' • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : Ψ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a' + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add, mul_smul, mul_comm k k', mul_smul k']
    exact Λ.add_mem (by rw [smul_comm k k']; exact Λ.nsmul_mem (hlat _ h1) k') (by rw [smul_comm k' k]; exact Λ.nsmul_mem (hlat' _ h2) k)

theorem isPlaceModel_comp_tensorHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ha' : a' * a' = a') (hb : b * b = b)
    (hab : a' * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf b Λ Ψ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 (T₀ (restrictHalf b a' Λ Ψ)) (T₀ ∘ₗ tensorHalf a' b Ψ) := by
  have hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) :=
    fun Φ hΦ => isSBHalf_tensorHalf ha' hb hΛ hΦ hΨ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have hxa : IsHalf (a' + b) x := (isHalf_iff' _ _).2 hax
    have e : tensorHalf a' b Ψ (fun t => Φ (t + x)) = fun t => tensorHalf a' b Ψ Φ (t + x) := by
      funext z
      simp only [tensorHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x hxa
  · have hy' : IsHalf (cA D (a' + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add, add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : tensorHalf a' b Ψ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * tensorHalf a' b Ψ Φ t := by
      funext z
      simp only [tensorHalf_apply]
      rw [GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, tensorHalf_halfInd]

end GlobalTheory.TwoStepModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSpherical
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isUnramChar_of_isCusp_of_isSpherical : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (x : IrrGL k), x.IsCusp → IsSpherical x.rep → x.IsUnramChar := by
  intro hG hBZ hZ k _ _ _ _ _ x hx hs
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have h1 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα
  have h2 : HasSupport x.rep {x} := hasSupport_self hx
  have he := GlobalTheory.T.supercuspidalSupport_unique_GL hG hBZ hZ k x _ _ h1 h2
  have hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i)) := by
    rw [he]; exact Multiset.mem_singleton_self x
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocksStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModule_in_stages_refined_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V),
    Nonempty (Representation.Equiv ((jac (refinePlace e e') π).comp (flatHom fun a b => GL (Fin (d' a b)) k))
      (relJacD e' (jac e π))) := by
  first | exact @GlobalTheory.JacStagesProof.jac_refinePlace_equiv | exact GlobalTheory.JacStagesProof.jac_refinePlace_equiv | (intros; apply GlobalTheory.JacStagesProof.jac_refinePlace_equiv <;> assumption)
end

