import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMemNonzeroLocusFibreOfSecBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFibre

open TwistLoc VVRank

theorem exists_clear_sval {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (M : Submonoid R)
    [IsLocalization M Rm] {X Y Y' : Scheme.{0}} {π : Y ⟶ Spec (CommRingCat.of R)}
    {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
    [CompactSpace Y] [QuasiSeparatedSpace Y] {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) (ε : K → ℤ)
    (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ t ∈ M, ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s (r ≫ h) z J = gc (r ≫ h ≫ π) z t * sval s' r z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨t, ht, s, hs⟩ := exists_clear_denominator M H hL φ ε s'
  refine ⟨t, ht, s, fun Z r z J hJ => ?_⟩
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact hs Z r z _ (hJ.mem (fun k => h ≫ φ k) r)

theorem exists_mem_nonzeroLocus_fibre : SecBaseChangeAnySt → ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsSecBasis _ (fun _ : Fin 1 => th) → ∀ s : Sp R, ∃ y ∈ nonzeroLocus th, P.A.hom ((snd (baseOver (Sp R)) P.A).left y) = s := by
  intro hS R _ P th hth s
  obtain ⟨V, hV, b, hb⟩ := ThetaReal.exists_univBasis hS P 1 le_rfl s
  have hp : s.asIdeal.IsPrime := s.isPrime
  let Rp := Localization.AtPrime s.asIdeal
  let k := IsLocalRing.ResidueField Rp
  let Tp : Over (Sp R) := Over.mk (spMap (algebraMap R Rp))
  let Tk : Over (Sp R) := Over.mk (spMap (IsLocalRing.residue Rp) ≫ spMap (algebraMap R Rp))
  let hk : Tk ⟶ Tp := Over.homMk (spMap (IsLocalRing.residue Rp)) rfl
  let u : Tp ⟶ baseOver (Sp R) := Over.homMk Tp.hom (Category.comp_id _)
  have hr : Set.range (spMap (algebraMap R Rp)) ⊆ Set.range V.ι := by
    rintro _ ⟨q, rfl⟩
    refine (Scheme.Opens.range_ι V).ge ?_
    refine Specializes.mem_open ?_ V.isOpen hV
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun x hx => ?_
    by_contra hx'
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
      (IsLocalization.map_units Rp (⟨x, hx'⟩ : s.asIdeal.primeCompl)))
  let v : Tp ⟶ overRes (T := baseOver (Sp R)) V := Over.homMk (IsOpenImmersion.lift V.ι _ hr) (by
    show IsOpenImmersion.lift V.ι _ hr ≫ V.ι ≫ 𝟙 _ = spMap (algebraMap R Rp)
    rw [Category.comp_id, IsOpenImmersion.lift_fac])
  let i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  let bp : LB.Sec (LPow P.A P.L 1 Tp) := pullS P.A _ v (SecM.toSec P.A (b i₀))
  have haff : IsAffine Tk.left := inferInstanceAs (IsAffine (Spec _))
  have hnt : Nontrivial Γ(Tk.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.domain_nontrivial
  obtain ⟨c, hc⟩ := hb Tk (hk ≫ v)
  have hne : (SecM.ofSec P.A (pullS P.A 1 hk bp) : SecM P.A P.L 1 Tk) ≠ 0 := fun h0 =>
    c.ne_zero i₀ ((hc i₀).trans ((pullM_comp P.A P.isLB _ hk v _).symm.trans h0))
  have hsm := P.isAb.smooth
  have hpr := P.isAb.proper
  have hred : IsReduced (Tk ⊗ P.A).left :=
    have : IsReduced Tk.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
    have : Smooth (fst Tk P.A).left := inferInstanceAs (Smooth (pullback.fst Tk.hom P.A.hom))
    GlobalTheory.isReduced_of_smooth_of_isReduced (fst Tk P.A).left
  obtain ⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 hk bp) := by
    by_contra hn
    exact hne (Subtype.ext (funext fun j => eq_zero_of_basicOpen_eq_bot ((pullS P.A 1 hk bp).f j)
      (eq_bot_iff.2 fun y hy => (hn ⟨y, TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩⟩).elim)))
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : QuasiSeparatedSpace P.A.left := (quasiSeparated_iff_quasiSeparatedSpace P.A.hom).mp inferInstance
  have H : IsPullback (snd Tp P.A).left (fst Tp P.A).left P.A.hom (spMap (algebraMap R Rp)) :=
    (IsPullback.of_hasPullback Tp.hom P.A.hom).flip
  obtain ⟨t, ht, σ, hσ⟩ := exists_clear_sval s.asIdeal.primeCompl H P.isLB (fun _ : Fin 1 => 𝟙 P.A.left)
    (fun _ => (snd Tp P.A).left) (fun _ => Category.comp_id _) (fun _ => 1) bp
  obtain ⟨a, ha, -⟩ := hth (pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) σ
    (snd (baseOver (Sp R)) P.A).left (fun _ => Category.comp_id _))
  choose J hJ using fun χ : (Tk ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ z)
  have hJ' : Good P.L z J := hJ
  let r : (Tk ⊗ P.A).left ⟶ (Tp ⊗ P.A).left := 𝟙 _ ≫ (hk ▷ P.A).left
  let ρ : (Tk ⊗ P.A).left ⟶ (baseOver (Sp R) ⊗ P.A).left := r ≫ (u ▷ P.A).left
  have e₁ : ρ ≫ (snd (baseOver (Sp R)) P.A).left = r ≫ (snd Tp P.A).left := by
    rw [Category.assoc, whisker_snd_left]
  have e₂ : r ≫ (snd Tp P.A).left ≫ P.A.hom = (fst Tk P.A).left ≫ Tk.hom := by
    rw [Category.assoc, Category.id_comp, ← Category.assoc, whisker_snd_left, Over.w, Over.w]
  have hs : ((fst Tk P.A).left ≫ Tk.hom) z = s := by
    show spMap (algebraMap R Rp) (spMap (IsLocalRing.residue Rp) ((fst Tk P.A).left z)) = s
    generalize (fst Tk P.A).left z = w
    obtain rfl : w = (IsLocalRing.closedPoint k : PrimeSpectrum k) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    have : spMap (IsLocalRing.residue Rp) (IsLocalRing.closedPoint k : PrimeSpectrum k) =
        (IsLocalRing.closedPoint Rp : PrimeSpectrum Rp) := IsLocalRing.comap_closedPoint (IsLocalRing.residue Rp)
    rw [this]
    exact PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := s.asIdeal))
  have u₁ : IsUnit (sv P.A bp r z J) := by
    rw [← sv_pullS P.A 1 hk bp (𝟙 _) z hJ']
    exact (AmpleSpan.mem_nonzeroLocus_iff_gs _ (𝟙 _) z (hJ'.mem (fun _ : Fin 1 => (snd Tk P.A).left) _)).1 hz
  have u₂ : IsUnit (gc (r ≫ (snd Tp P.A).left ≫ P.A.hom) z t) := by
    rw [gc, AmpleSpan.isUnit_gs_iff _ z ⊤ trivial, e₂, hs]
    exact (basicOpen_eq_of_affine (R := CommRingCat.of R) t).ge ht
  have u₃ := u₂.mul u₁
  have hm := hJ'.mem (fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) ρ
  have e₃ := IsComb.gs (π := (fst (baseOver (Sp R)) P.A).left) ha ρ z _ hm
  rw [Fin.sum_univ_one] at e₃
  have e₄ := sval_pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) σ
    (snd (baseOver (Sp R)) P.A).left (fun _ => Category.comp_id _) ρ z hJ'
  rw [e₁, hσ _ r z J hJ'] at e₄
  refine ⟨ρ z, (AmpleSpan.mem_nonzeroLocus_iff_gs th ρ z hm).2
    (isUnit_of_mul_isUnit_right ((congrArg IsUnit (e₃.symm.trans e₄)).mpr u₃)), ?_⟩
  show ((ρ ≫ (snd (baseOver (Sp R)) P.A).left) ≫ P.A.hom) z = s
  rw [e₁, Category.assoc, e₂, hs]

end GlobalTheory.ThetaFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPadicLiftTorsionPointInvertibleOrder
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ZJ.exists_torsion_lift_of_residue :
    ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  intro p _ B G _ hG y n hn t ht
  have := hG.comm
  have := hG.smooth
  have := GrpTangent.etale_torsion G hn
  have hP := GrpTangent.isPullback_torsion G n
  have e : ∀ {T : Scheme.{0}} (q : T ⟶ B), (1 : Over.mk q ⟶ G).left = q ≫ η[G].left := by
    intro T q
    rw [Hom.one_def, Over.comp_left]; rfl
  have w : t.left ≫ (mulN G n).left =
      (spMap (IsLocalRing.residue (OO p)) ≫ y) ≫ η[G].left := by
    rw [← Over.comp_left, GrpTangent.comp_mulN, ht, e]
  obtain ⟨c, hc₁, hc₂⟩ := ZJ.exists_classical_lift_of_smooth p _ _ (torsion G n).hom y
    (hP.lift _ _ w) (hP.lift_snd _ _ w)
  let b : Over.mk y ⟶ G := Over.homMk (c ≫ (torsion.ι G n).left) (by
    rw [Category.assoc, Over.w]; exact hc₁)
  refine ⟨b, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [← GrpTangent.comp_mulN, Over.comp_left, e]
    change (c ≫ (torsion.ι G n).left) ≫ _ = _
    rw [Category.assoc, hP.w, ← Category.assoc, hc₁]
  · change _ ≫ c ≫ (torsion.ι G n).left = _
    rw [← Category.assoc]
    exact (congrArg (· ≫ (torsion.ι G n).left) hc₂).trans (hP.lift_fst _ _ w)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFieldsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullDeg_cancel_tower_of_fields : ∀ (K₀ K₁ K : Type) [Field K₀] [Field K₁] [Field K] (α : K₀ →+* K₁) (β : K₁ →+* K) (D₀ : DegPre K₀) (D₁ : DegPre K₁) (D : DegPre K) (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D), ∃ hD : IsPullDeg β D₁ D, PsiEvenPull.proj hD ≫ PsiEvenPull.proj h₁ = PsiEvenPull.proj h := by
  first | exact @GlobalTheory.FieldPull.exists_isPullDeg_cancel | exact GlobalTheory.FieldPull.exists_isPullDeg_cancel | (intros; apply GlobalTheory.FieldPull.exists_isPullDeg_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionReduction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero_eq_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val _ _ _ τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

def chartPullH {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) :
    ChartPull (Φ.H 1) (LB.LinComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ))) (𝟙 _) :=
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l _ hy => Set.mem_iInter.2 fun _ => c.le l hy
  { idx := fun l _ => c.idx l
    le := le
    g := fun y l l' hl hl' => by
      refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) (𝟙 _) y _ _
        (le l hl) (le l' hl')).symm
      have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hl hl'
      have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hl, hl'⟩ (Φ.N₀.g l l')
      refine (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).trans (Eq.symm ?_)
      refine Eq.trans ?_ (map_pow _ _ _).symm
      refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
      rw [Category.assoc]
      rfl }

theorem trF_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (q : Y' ⟶ Y) (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (j j' : K → L.ι) :
    trF (fun a => q ≫ ψ a) ε r z j j' = trF ψ ε (r ≫ q) z j j' := by
  simp only [trF, Category.assoc]

theorem exists_red_of_pure : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ b : LB.Sec (LB.LinComb L ψ ε), UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF α hw φ hp
  have := Φ.D.q_hom
  have := Φ.D.q_flat
  have := Φ.D.q_surjective
  obtain ⟨s, hs⟩ := exists_sec_of_refine _ _ _ (Φ.H_isLB 1) (DVR.linComb_isLB L hL _ _) (chartPullH Φ c) φ
  have hF' : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ Φ.D.q.left ≫ π) φt)
      (Sum.elim (fun _ => (N : ℤ)) (fun a => - εt a)) (fun a => Φ.D.q.left ≫ ψ a) ε := by
    intro U _ h
    have e := hF U h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_neg,
      Finset.prod_inv_distrib] at e ⊢
    rw [← e, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF' (pullMulSec s (𝟙 _) (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have vσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
      r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
      gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval σ r z J * (val t r z J).val := by
    intro Z r z J hJ l hl e
    rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, val_inv, Category.comp_id, Units.inv_mul_cancel_right,
      sval_of s r z J (fun _ => c.idx l) (fun _ => e)]
    exact hs l Z r z hl
  have le : ∀ j : K → L.ι, Φ.D.q.left ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j :=
    fun j y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Φ.E.B.left, LB.wchart L ψ j),
      (Φ.D.q.left.app _).hom a = (Φ.G.left.presheaf.map (homOfLE (le j)).op).hom (σ.f j) := by
    intro j
    refine exists_app_eq_of_hasWt_zero k Φ.E Φ.G Φ.D _ _ fun Z τ g z hz => ?_
    have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
      congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
    have hz' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left (g.left z))
    have hl' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hl
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hl)
    have hwt : HasWt Φ.D.i _ (φ.f l) α :=
      (PureWt.hasWt_iff_weight k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).2 fun χ hne => by
        by_contra h
        exact hne (hp ⟨l, h⟩)
    have h₀ := hwt Z τ g z hl
    have h₁ := vσ _ g.left z J hJ l hl (e ())
    have h₂ := vσ _ ((τ ≫ Φ.D.i) * g).left z J hJ l hl' (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
    have h₃ : sval σ ((τ ≫ Φ.D.i) * g).left z J = sval σ g.left z J := by
      have h₄ := h₂.symm.trans (h₀.trans (congrArg _ h₁))
      rw [hw Z τ g z J hJ, mul_left_comm, ← Units.val_mul] at h₄
      exact (Units.mul_left_inj _).1 h₄
    rw [gm_charUnit_zero_eq_one, Units.val_one, _root_.one_mul]
    refine (gs_res _ z (le j) hz' _).trans (Eq.trans ?_ (gs_res _ z (le j) hz _).symm)
    refine (sec_trans σ _ z (le j hz') (hJ.mem _ _)).trans (Eq.trans ?_ (sec_trans σ _ z (le j hz) (hJ.mem _ _)).symm)
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) h₃
    simp only [trF_comp, ← Category.assoc, hq]
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z), Φ.D.q.left (r z) ∈ LB.wchart L ψ j →
      gs (r ≫ Φ.D.q.left) z (LB.wchart L ψ j) (a j) =
        gs r z (LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j) (σ.f j) := fun j Z r z hz =>
    (gs_pull r _ z _ hz _).symm.trans ((congrArg (gs r z _) (ha j)).trans (gs_res r z (le j) hz _))
  refine ⟨⟨a, fun j j' => FunDescent.app_injective Φ.D.q.left (LB.wchart L ψ j ⊓ LB.wchart L ψ j')
    (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ l hl e => ?_⟩
  · have hy' : Φ.D.q.left y ∈ LB.wchart L ψ j ⊓ LB.wchart L ψ j' := hy
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).symm)
    refine ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (sec_trans σ (𝟙 _) y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (gs_mul (𝟙 _ ≫ Φ.D.q.left) y _ hy' _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (congrArg Units.val
        ((gm_linComb L ψ ε (𝟙 _ ≫ Φ.D.q.left) y j j' hy'.1 hy'.2).trans (trF_comp _ _ _ _ _ _ _).symm)))
      ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  · refine (vσ Z r z J hJ l hl e).trans (congrArg₂ (· * ·) (Eq.symm ?_) rfl)
    rw [sval_of _ (r ≫ Φ.D.q.left) z J (fun a => J (r ≫ Φ.D.q.left ≫ ψ a)) (fun a => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun a => hJ (r ≫ Φ.D.q.left ≫ ψ a))

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamilyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratio_descends_degenerationPsiFamily : ∀ (K : Type) [Field K] (D : DegPre K) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen), ∃ a : D.X → K, ∀ (K₁ : Type) [Field K₁] (β : K₁ →+* K) (D₁ : DegPre K₁) (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ)), (∀ χ, a χ ∈ Set.range β) → ∃ (ψ₁ : TauTwist.PsiFam D₁) (hψ₁ : ∀ χ, (ψ₁ χ).IsGen) (hD : IsPullDeg β (TauTwist.withPsi D₁ ψ₁ hψ₁) D), PsiEvenPull.proj hD = PsiEvenPull.proj h := by
  first | exact @GlobalTheory.FieldPull.exists_ratio_descends | exact GlobalTheory.FieldPull.exists_ratio_descends | (intros; apply GlobalTheory.FieldPull.exists_ratio_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_resG_apply {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_secOn_glue {X : Scheme.{0}} (B : LB X) (V : X.Opens) {κ : Type} (T : κ → X.Opens)
    (hT : ∀ k, T k ≤ V) (hV : ∀ x ∈ V, ∃ k, x ∈ T k) (σ : ∀ k j, Γ(X, T k ⊓ B.U j))
    (hσ : ∀ k, σ k ∈ secOn B (T k))
    (hc : ∀ k k' j, resG X (inf_le_inf_right _ inf_le_left : (T k ⊓ T k') ⊓ B.U j ≤ T k ⊓ B.U j) (σ k j) =
      resG X (inf_le_inf_right _ inf_le_right : (T k ⊓ T k') ⊓ B.U j ≤ T k' ⊓ B.U j) (σ k' j)) :
    ∃ τ ∈ secOn B V, ∀ k j, resG X (inf_le_inf_right _ (hT k)) (τ j) = σ k j := by
  have H : ∀ j, ∃ τ : Γ(X, V ⊓ B.U j), ∀ k, resG X (inf_le_inf_right _ (hT k)) τ = σ k j := fun j => by
    obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' (fun k => T k ⊓ B.U j) (V ⊓ B.U j)
      (fun k => homOfLE (inf_le_inf_right _ (hT k)))
      (fun x hx => by
        obtain ⟨k, hk⟩ := hV x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hx.2⟩) (fun k => σ k j) (fun k k' => by
        have e : (T k ⊓ B.U j) ⊓ (T k' ⊓ B.U j) ≤ (T k ⊓ T k') ⊓ B.U j :=
          fun x hx => ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
        have := congrArg (resG X e) (hc k k' j)
        rw [resG_resG_apply, resG_resG_apply] at this
        exact this)
    exact ⟨g, hg⟩
  choose τ hτ using H
  refine ⟨τ, fun i j => ?_, fun k j => hτ j k⟩
  refine X.sheaf.eq_of_locally_eq' (fun k => T k ⊓ B.U i ⊓ B.U j) (V ⊓ B.U i ⊓ B.U j)
    (fun k => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hT k))))
    (fun x hx => by
      obtain ⟨k, hk⟩ := hV x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ⟨hk, hx.1.2⟩, hx.2⟩) _ _ fun k => ?_
  have h := hσ k i j
  rw [← hτ i k, ← hτ j k, resG_resG_apply, resG_resG_apply] at h
  change resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _ =
    resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _
  rw [map_mul, resG_resG_apply, resG_resG_apply, resG_resG_apply]
  exact h

theorem sum_mul_mem_secOn {X : Scheme.{0}} (B : LB X) (V : X.Opens) {I : Type} [Fintype I] (f : I → Γ(X, V))
    (σ : I → ∀ j, Γ(X, V ⊓ B.U j)) (hσ : ∀ i, σ i ∈ secOn B V) :
    (fun j => ∑ i, resG X inf_le_left (f i) * σ i j) ∈ secOn B V := fun j j' => by
  simp only [map_sum, map_mul, Finset.mul_sum, resG_resG_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hσ i j j', mul_left_comm]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem ZHPre.genVal_res (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V V' : Q.G.left.Opens} (e : V' ≤ V)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V' (fun j => resG _ (inf_le_inf_right _ e) (σ j)) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  rw [h K β g r jP jL h1 h2 h3 h4 (h5.trans e)]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (V' ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact (valR_res (g ≫ Q.φ) _ hU _).symm

theorem ZHPre.genVal_of_cover (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V : Q.G.left.Opens} {κ : Type}
    (T : κ → Q.G.left.Opens) (hT : ∀ a, T a ≤ V) (hV : ∀ x ∈ V, ∃ a, x ∈ T a)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ a, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c (T a)
      (fun j => resG _ (inf_le_inf_right _ (hT a)) (σ j))) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  obtain ⟨a, ha⟩ := hV _ (h5 ⟨IsLocalRing.closedPoint K, rfl⟩)
  have h6 : Set.range (g ≫ Q.φ) ⊆ T a := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) w (IsLocalRing.closedPoint K)]
    exact ha
  rw [h a K β g r jP jL h1 h2 h3 h4 h6]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (T a ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h6 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact valR_res (g ≫ Q.φ) _ hU _

theorem ZHPre.genVal_sum (k : ℤ) {I J : Type} [Fintype I] [Fintype J]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : J → I → Ω) (W : M.Z.Opens)
    (hW : (W : Set M.Z).Nonempty) (f : J → Γ(M.Z, W))
    (σ : J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ i, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (c i) _ (σ i)) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (fun l => ∑ i, valF M.pt W (f i) * c i l) _
      (fun j => ∑ i, resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i)) * σ i j) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  have hV : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W) := fun w _ => h5 ⟨w, rfl⟩
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [Category.assoc, Q.cart.1.w, ← h1]
    rfl
  have hf : ∀ i, (valMap (g ≫ Q.φ) _ hU).hom (resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i))) =
      β (valF M.pt W (f i)) := fun i => by
    rw [← valR_eq, valR_res _ _ hU, valR_appLE _ _ _ hV, hp, valR_spMap_comp β M.pt W (M.top_le_preimage_pt hW),
      valF_eq_valR]
  have hi := fun i => h i K β g r jP jL h1 h2 h3 h4 h5
  rw [valF_eq_valR (g ≫ Q.φ), valR_eq _ _ hU, map_sum, Finset.mul_sum]
  simp only [map_sum, map_mul, Finset.sum_mul, hf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, ← valR_eq, ← valF_eq_valR, ← hi i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _

end GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_secOn_genVal_of_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  intro o Ω _ _ _ S ρ M U₀ EE Q hU hb W x₀ v hv
  have H : ∀ z : W, ∃ T : M.Z.Opens, z.1 ∈ T ∧ T ≤ W ∧
      ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ T),
        GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
    rintro ⟨z, hz⟩
    obtain ⟨U, b, hzU, -, hE⟩ := EE.loc z
    have h1 := (hv z hz).2
    rw [hE z hzU] at h1
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun i l => b i l)).1 h1
    let T : M.Z.Opens := W ⊓ U ⊓ ⟨⋂ i, {z' | (a i : Ω) ∈ M.O z'},
      isOpen_iInter_of_finite fun i => M.isOpen_setOf_mem_O _⟩
    have hzT : z ∈ T := ⟨⟨hz, hzU⟩, Set.mem_iInter.2 fun i => (a i).2⟩
    have hne : (T : Set M.Z).Nonempty := ⟨z, hzT⟩
    have h2 : ∀ i, ∃ f : Γ(M.Z, T), valF M.pt T f = a i := fun i =>
      (RatModel.mem_ringOn_iff_exists hne).1 (RatModel.mem_ringOn.2 fun z' hz' => Set.mem_iInter.1 hz'.2 i)
    choose f hf using h2
    obtain ⟨σ, hσ⟩ := hb T x₀ b fun z' hz' => ⟨(hv z' hz'.1.1).1, hE z' hz'.1.2⟩
    refine ⟨T, hzT, inf_le_left.trans inf_le_left, _,
      sum_mul_mem_secOn _ _ (fun i => (Q.G.hom.appLE T _ le_rfl).hom (f i)) σ fun i => (hσ i).1, ?_⟩
    have h3 := Q.genVal_sum S.N ρ.s (fun i l => b i l / S.th x₀) T hne f σ fun i => (hσ i).2
    have h4 : (fun l => ∑ i, valF M.pt T (f i) * (b i l / S.th x₀)) = fun l => v l / S.th x₀ := by
      funext l
      rw [← ha, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf, ← mul_div_assoc]
      rfl
    rw [h4] at h3
    exact h3
  choose T hz hT σ hσ hg using H
  have hle : ∀ z, Q.G.hom ⁻¹ᵁ T z ≤ Q.G.hom ⁻¹ᵁ W := fun z x hx => hT z hx
  have hcov : ∀ x ∈ Q.G.hom ⁻¹ᵁ W, ∃ z, x ∈ Q.G.hom ⁻¹ᵁ T z := fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩
  obtain ⟨τ, hτ, hr⟩ := exists_secOn_glue _ (Q.G.hom ⁻¹ᵁ W) (fun z => Q.G.hom ⁻¹ᵁ T z) hle hcov σ hσ
    fun z z' j => congrFun (Q.eq_of_genVal hU _ _ _ _ _ _ (Q.genVal_res _ _ _ inf_le_left _ (hg z))
      (Q.genVal_res _ _ _ inf_le_right _ (hg z'))) j
  refine ⟨τ, hτ, Q.genVal_of_cover _ _ _ _ hle hcov τ fun z => ?_⟩
  have h5 := hg z
  rw [← funext (hr z)] at h5
  exact h5

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPullbackMulGeneratorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pullback_mul_generator : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ b : LB.Sec (LB.LinComb L ψ ε), ∃ φ : (Φ.H 1).Sec, UFib.Red Φ c t b φ := by
  first | exact @GlobalTheory.ZH.UFib.exists_red | exact GlobalTheory.ZH.UFib.exists_red | (intros; apply GlobalTheory.ZH.UFib.exists_red <;> assumption)
end

