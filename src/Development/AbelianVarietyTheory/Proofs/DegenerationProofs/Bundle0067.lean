import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpansionCoefMemAdicPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem eq_zero_of_cst_eq_zero {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} (p : X ⟶ Sp S) [Flat p] (x : X)
    (hx : p x = IsLocalRing.closedPoint S) {a : S} (ha : cst p x a = 0) : a = 0 := by
  let φ : S →+* X.presheaf.stalk x := (p.stalkMap x).hom.comp
    (((Sp S).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
  have hφ : ∀ c, φ c = cst p x c := fun c => by
    rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  have fl : φ.Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)) ?_) (Flat.stalkMap p x)
    have hU := isAffineOpen_top (Sp S)
    let _ := (Sp S).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
    have := hU.isLocalization_stalk ⟨p x, trivial⟩
    exact IsLocalization.flat ((Sp S).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp S).Opens)) : Sp S))
      (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl
  let _ := φ.toAlgebra
  have : Module.Flat S (X.presheaf.stalk x) := fl
  have : IsLocalHom (algebraMap S (X.presheaf.stalk x)) := ⟨fun c hc => by
    by_contra h
    exact cst_not_isUnit p x hx h (hφ c ▸ hc)⟩
  have : Module.FaithfullyFlat S (X.presheaf.stalk x) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective S (X.presheaf.stalk x) ((hφ a).trans (ha.trans (map_zero _).symm))

theorem coef_mem_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  intro R _ _ _ I hI D A G _ _ U σ f th hE hth e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun χ hχ u b hb => ?_⟩
  have hI' : I ^ (e + 1) ≠ ⊤ := fun h => hI (top_unique (h ▸ Ideal.pow_le_self e.succ_ne_zero))
  haveI : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
  haveI : IsLocalRing (R ⧸ I ^ (e + 1)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk (I ^ (e + 1))) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcl : thick R I e (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (I ^ (e + 1)))
  haveI := U.semi.smooth
  haveI : Flat (thickObj R I e G).hom := inferInstanceAs (Flat (pullback.snd G.hom (thick R I e)))
  obtain ⟨z₀, hz₀, hnz⟩ := hth (IsLocalRing.closedPoint R)
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  let y : T ⟶ D.P.A := (U.gt e).pG
  let m : 𝟙_ _ ⊗ D.P.A ⟶ D.P.A := snd (𝟙_ _) D.P.A * (cT D _ χ)⁻¹
  let τ : D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (toUnit _) (𝟙 _ * cT D _ χ)
  have hc : ∀ {T₁ T₂ : Over (Spec (CommRingCat.of R))} (g : T₁ ⟶ T₂), g ≫ cT D _ χ = cT D _ χ := fun g => by
    rw [cT, ← Category.assoc, toUnit_unique (g ≫ toUnit _) (toUnit _)]
  have hmτ : m ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, inv_mul_cancel_right, Category.id_comp]
  have hyτ : y ≫ τ = lift (toUnit T) (y * cT D T χ) := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, lift_snd]
  have h1 : D.P.A.hom (m.left z₀) = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, Over.w m]; exact hz₀
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.P.A.hom) (g := thick R I e)
    (m.left z₀) (IsLocalRing.closedPoint (R ⧸ I ^ (e + 1))) (h1.trans hcl.symm)
  obtain ⟨z, rfl⟩ := (U.gt e).q_surj.1 w
  have hy : y.left z = m.left z₀ := hw
  have hz : (thickObj R I e G).hom z = IsLocalRing.closedPoint _ := by
    rw [← Over.w (U.gt e).q, Scheme.Hom.comp_apply]; exact hw'
  have h2 : (lift (toUnit T) (y * cT D T χ)).left z = z₀ := by
    rw [← hyτ, Over.comp_left, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, ← Over.comp_left, hmτ]
    rfl
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
  obtain ⟨JG, hJG⟩ := exists_good_pt (Z := T.left) U.P.L.isLB z
  have hu := (MulPullSec.mem_nonzeroLocus_iff th (lift (toUnit T) (y * cT D T χ)).left z hJ).1 (h2 ▸ hnz)
  have h0 := (hs T.left (𝟙 _) (lift (toUnit T) (fstG I e G)).left (lift (toUnit T) y).left
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z JG J hJG hJ).1 χ hχ
  have h3 := hb T y z J hJ
  rw [h0] at h3
  have h4 : cst T.hom z b = 0 := ((Units.isUnit _).mul hu).mul_left_eq_zero.1 h3.symm
  have h5 : cst (thickObj R I e G).hom z (Ideal.Quotient.mk _ b) = 0 :=
    (cst_comp (thickObj R I e G).hom (Ideal.Quotient.mk (I ^ (e + 1))) z b).symm.trans h4
  exact Ideal.Quotient.eq_zero_iff_mem.1 (eq_zero_of_cst_eq_zero _ z hz h5)

end GlobalTheory.PsiRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ForallTermNeZeroOfPsiRelation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory

theorem psiRel_field_ne_zero_iff {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (s : Raw D F 1) (h : PsiRel D (TF (R := R) F) s) (χ : D.X) :
    (∃ j, (s χ).f j ≠ 0) ↔ ∃ j, (s 0).f j ≠ 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := (DegPre.BF D F).left) D.P.isLB (genericPoint _)
  have := PsiExists.isIso_trF D F χ
  have : IsIso (DegPre.trF D F χ).left := inferInstanceAs (IsIso ((Over.forget _).map (DegPre.trF D F χ)))
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have e := h χ (DegPre.BF D F) (fst _ _) κ (snd _ _) _ J hJ
  have e₁ : (lift (fst (TF (R := R) F) D.P.A) (snd _ _)).left = 𝟙 (DegPre.BF D F).left :=
    congrArg (fun q : DegPre.BF D F ⟶ DegPre.BF D F => q.left) lift_fst_snd
  have e₂ : sval (s χ) (𝟙 (DegPre.BF D F).left) (genericPoint _) J =
      (val (D.psi χ) κ.left (genericPoint _) J * rigV D (T := DegPre.BF D F) (genericPoint _) J).val *
        sval (s 0) (DegPre.trF D F χ).left (genericPoint _) J :=
    (congrArg (fun q => sval (s χ) q (genericPoint _) J) e₁).symm.trans e
  rw [exists_ne_zero_iff_sval_ne_zero _ hJ, e₂]
  constructor
  · intro h0
    by_contra hn
    simp only [not_exists, not_not] at hn
    exact h0 (by rw [sval_eq_zero_of_local_eq_zero (s 0) hn _ _ J hJ, MulZeroClass.mul_zero])
  · intro h0
    exact mul_ne_zero (Units.ne_zero _) (sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s 0) h0 _ _ _ J hJ)

theorem forall_ne_zero_of_psiRel : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiRel D (𝟙_ _) f → (∃ α j, (f α).f j ≠ 0) → ∀ α, ∃ j, (f α).f j ≠ 0 := by
  rintro R _ _ D f h ⟨α, hα⟩ β
  obtain ⟨s, hs⟩ := PsiExists.exists_pullB D (FractionRing R) (toUnit _) 1 f
  have h' := psiRel_of_pullB R D _ f s hs h
  have i := pullB_ne_zero_iff R D _ 1 f s hs
  exact (i β).1 ((psiRel_field_ne_zero_iff D _ s h' β).2 ((psiRel_field_ne_zero_iff D _ s h' α).1 ((i α).2 hα)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorusPerp

section Pairing
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.TorusWeight GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem weilQkIs_tor (hG : GlobalFnsSt) {k : ℕ} (p p' : QkPt D F k) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) : WeilQkIs D F k p p' (τ (Multiplicative.ofAdd p'.y)).val := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
  rw [phiRel_iff hG _ _ hw'] at h₁ h₄
  rw [phiRel_iff hG _ _ hw] at h₂ h₃
  have tr : DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]; exact tr_fst D F _
    · rw [Category.id_comp]
      refine (tr_pr D F _).trans ?_
      rw [hτ.1, MonObj.comp_one, _root_.mul_one]
  have v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      (uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd α)).val) *
          (val w (ρ ≫ fst _ _).left z J).val := by
    intro α T ρ z J hJ
    have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have hu : uVal D F k α p.g.b ρ z J = 1 := by
      rw [uVal, hτ.1]
      simp only [MonObj.comp_one]
      unfold cubN
      simp only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]
    have e := val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ
    rw [hu, _root_.one_mul, val_mul hJ, Units.val_mul, e]
  intro β
  obtain ⟨α, rfl⟩ : ∃ α, α + p'.y = β := ⟨β - p'.y, sub_add_cancel _ _⟩
  refine (sval_const _ _ _ _).2 fun T ρ z J hJ => ?_
  have e₁ := h₁ α _ rfl T ρ z J hJ
  have e₂ := h₂ (α + p'.y) (α + p'.y) (by rw [hy, add_zero]) T ρ z J hJ
  have e₃ := h₃ α α (by rw [hy, add_zero]) T (ρ ≫ DegPre.trPt D F p'.g.b) z J hJ
  have e₄ := h₄ α _ rfl T ρ z J hJ
  rw [v _ T _ z J hJ, tr, Category.comp_id] at e₂ e₃
  rw [Category.assoc, tr_fst] at e₃
  rw [e₂, e₄, e₃, e₁, ofAdd_add, map_mul, Units.val_mul (τ _), map_mul, gs_mul _ _ ⊤ trivial]
  ring

attribute [local instance] gtGroup in

theorem exists_qkPt_tor (hB : D.TauBimult) {k : ℕ} (τ : Multiplicative D.X →* Fˣ) (h : τ ^ k = 1) :
    ∃ p : QkPt D F k, p.y = 0 ∧ IsTor τ p.g :=
  ⟨qkMk hB 0 (torusPt D F (Additive.ofMul τ)) (by rw [← map_nsmul, ← ofMul_pow, h, ofMul_one, map_zero, map_zero]),
    rfl, (isTor_iff _ _).2 (isTorusPtF_torusPt τ)⟩

end Pairing

section Algebra

theorem eStd_add_left (g n : ℕ) (a a' b : Fin g ⊕ Fin g → ZMod n) :
    eStd g n (a + a') b = eStd g n a b + eStd g n a' b := by
  simp only [eStd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eStd_add_right (g n : ℕ) (a b b' : Fin g ⊕ Fin g → ZMod n) :
    eStd g n a (b + b') = eStd g n a b + eStd g n a b' := by
  simp only [eStd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eq_zero_of_eStd (g n : ℕ) (a : Fin g ⊕ Fin g → ZMod n) (h : ∀ b, eStd g n a b = 0) : a = 0 := by
  funext j
  rcases j with i | i
  · simpa [eStd, Pi.single_apply] using h (Pi.single (.inr i) 1)
  · simpa [eStd, Pi.single_apply] using h (Pi.single (.inl i) 1)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem isoFree_perp_ker {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy)
    (H : ∀ l : X →+ ZMod (S.r * S.N), ∃ a ∈ yy.ker, ∀ b α, yy b = QuotientAddGroup.mk α → eStd S.g _ a b = l α) :
    S.IsoFree (S.perp yy.ker) ∧ ∃ wt : X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : X),
      yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker,
        wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ (t : S.perp yy.ker) (b b' : S.Gam), yy b = yy b' → eStd S.g _ t b = eStd S.g _ t b' := by
    intro t b b' e
    have h0 : eStd S.g _ t (b - b') = 0 := t.2 _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  let Λ : S.perp yy.ker →+ X →+ ZMod (S.r * S.N) := AddMonoidHom.mk'
    (fun t => AddMonoidHom.mk' (fun α => eStd S.g _ t (σ α)) fun α β => by
      rw [← eStd_add_right]
      exact ind t _ _ (by rw [map_add, hσ, hσ, hσ, QuotientAddGroup.mk_add]))
    fun t t' => AddMonoidHom.ext fun α => eStd_add_left _ _ _ _ _
  have hΛ : ∀ (t : S.perp yy.ker) b α, yy b = QuotientAddGroup.mk α → Λ t α = eStd S.g _ t b :=
    fun t b α e => ind t _ _ ((hσ α).trans e.symm)
  have hbij : Function.Bijective Λ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => Subtype.ext (eq_zero_of_eStd _ _ _ fun b => ?_), fun l => ?_⟩
    · obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy b)
      rw [← hΛ t b α e.symm, ht, AddMonoidHom.zero_apply]
    · obtain ⟨a, -, ha⟩ := H l
      exact ⟨⟨a, fun h hh => (ha h 0 hh).trans (map_zero l)⟩, AddMonoidHom.ext fun α => ha _ _ (hσ α)⟩
  refine ⟨⟨fun s hs t ht => ?_, Module.finrank ℤ X, ⟨(AddEquiv.ofBijective Λ hbij).trans
    ((addMonoidHomLequivInt ℤ).toAddEquiv.trans ((Module.finBasis ℤ X).constr ℤ).symm.toAddEquiv)⟩⟩,
    Λ.flip.compr₂ (ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom, fun x α e t => ?_⟩
  · obtain ⟨a, ha, hl⟩ := H (Λ ⟨s, hs⟩)
    obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy t)
    rw [← hΛ ⟨s, hs⟩ t α e.symm, ← hl t α e.symm, GlobalTheory.ThetaProj.eStd_swap, ht a ha, neg_zero]
  · rw [← hΛ t x α e]; rfl

end Algebra

section Points

def ptHom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem ptHom_bijective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (ptHom h T) :=
  ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm)),
    fun z => ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (β : A →+* B) (c : Aˣ) :
    Units.map (spMap β).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map β.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem unitOn_injective {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1 (congrArg Units.val h))

end Points

theorem isoFree_perp_and_weights : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → S.IsoFree (S.perp yy.ker) ∧ ∃ wt : u.D.toPre.X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : u.D.toPre.X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker, wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  intro hL _ hT o Ω _ _ _ hA S ρ p _ y₀ u yy hs hyy
  have hG := hL.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have := ρ.P.isAb.comm
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit hn.ne).unit
  let ω : (PadicAlgCl p)ˣ := Units.map y₀.toMonoidHom c₀
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map

  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ :=
    (Spec.map_comp _ _).symm.trans (congrArg spMap u.fac)
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  let Φ := ptHom u.cart (TFK (R := u.V) (PadicAlgCl p))
  have hΦ : Function.Bijective Φ := ptHom_bijective _ _
  have lab : ∀ a q, Φ (f q) = h ≫ ρ.pt a → yy a = QuotientAddGroup.mk q.y := fun a q e =>
    hyy a q _ ((f₁ _ _).2 rfl) ((congrArg (fun z => z.left) e).trans (by rw [← hh]; rfl))
  let pt : Multiplicative S.Gam →* (baseOver (Sp S.R) ⟶ ρ.P.A) := MonoidHom.mk' (fun a => ρ.pt a.toAdd) fun _ _ => ρ.pt_add _ _
  have onto : ∀ b, ∃ q, Φ (f q) = h ≫ ρ.pt b := fun b => by
    obtain ⟨x, hx⟩ := hΦ.2 (h ≫ ρ.pt b)
    obtain ⟨q, rfl⟩ := f₂ x (hΦ.1 (by
      have e : ρ.pt b ^ (S.r * S.N) = 1 := by
        refine (map_pow pt (Multiplicative.ofAdd b) _).symm.trans ?_
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul, ofAdd_zero, map_one]
      rw [map_pow, hx, map_one, ← MonObj.comp_pow, e, MonObj.comp_one]))
    exact ⟨q, hx⟩
  have weil : ∀ a b q q', Φ (f q) = h ≫ ρ.pt a → Φ (f q') = h ≫ ρ.pt b →
      WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (f q) (f q') (unitOn (ω ^ (eStd S.g _ a b).val)) := fun a b q q' e e' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h (ρ.weil a b (c₀ ^ (eStd S.g _ a b).val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← e, ← e'] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb _ _ _ _
      (Φ (f q)) (Φ (f q')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  refine isoFree_perp_ker S yy hs fun l => ?_
  let χ := AddChar.zmodChar (S.r * S.N) hω.pow_eq_one
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ := χ.toMonoidHom.comp l.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (l α).val := fun _ => rfl
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) (k := S.r * S.N) u.D.tau_bimult τ (MonoidHom.ext fun α => by
    show (ω ^ (l α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) _ (Φ (f q)) (by rw [← map_pow, hq1, map_one])
  refine ⟨a, (lab a q ha.symm).trans (by rw [hq]; rfl), fun b α e => ?_⟩
  obtain ⟨q', hq'⟩ := onto b
  have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB (weil a b q q' ha.symm hq')
    ((f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)))
  rw [hτ] at e₁
  rw [ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)]
  obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 ((lab b q' hq').symm.trans e)
  have hz' : (S.r * S.N) • z = -q'.y + α := hz
  have := congrArg l hz'
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_add, map_neg] at this
  exact neg_add_eq_zero.1 this.symm

end GlobalTheory.ZH.TorusPerp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointExtendsTorsionPointMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem grpPullback_mul_section {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (H : IsGrpPullback G' G f φ) (x y : baseOver B' ⟶ G')
    (h h' : baseOver B ⟶ G) (hx : x.left ≫ φ = f ≫ h.left) (hy : y.left ≫ φ = f ≫ h'.left) :
    (x * y).left ≫ φ = f ≫ (h * h').left := by
  let U : Over.mk ((baseOver B').hom ≫ f) ⟶ baseOver B := Over.homMk f (by simp)
  have e := H.2 (baseOver B') x y (U ≫ h) (U ≫ h') hx.symm hy.symm
  rw [← MonObj.comp_mul] at e
  exact e.symm

theorem extends_mul (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ)
    [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a b : S.Gam) (h h' : baseOver (Sp u.V) ⟶ u.G)
    (ha : Extends u a h) (hb : Extends u b h') : Extends u (a + b) (h * h') := by
  obtain ⟨x, x1, x2, x3⟩ := ha
  obtain ⟨y, y1, y2, y3⟩ := hb
  have := u.U.gen_hom
  let X : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk x x2
  let Y : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk y y2
  refine ⟨(X * Y).left, ?_, Over.w (X * Y), ?_⟩
  · exact grpPullback_mul_section (isGrpPullback_pullback u.G (jK u.V)) X Y h h' x1 y1
  · rw [ρ.pt_add]
    exact grpPullback_mul_section
      (((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl) X Y _ _ x3 y3

end GlobalTheory.UnitTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev FrAt (x : TFK (R := R) F ⟶ A.A) : Type :=
  LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))

def ValAt {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def IsComb {k : ℕ} {J : Type} [Fintype J] (t : J → SecA A F k) (b : J → F) (σ : SecA A F k) : Prop :=
  ∀ j, σ.f j = ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b l)) * (t l).f j
end
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

structure ThetaSys.Real.UTest.Geom (u : ρ.UTest p y₀) where
  pt : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
  pt_over : ∀ a, (pt a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left
  pt_add : ∀ a b, pt (a + b) = pt a * pt b
  pt_bij : ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃! a, pt a = z
  weil : ∀ a b (c : (PadicAlgCl p)ˣ),
    (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) →
    WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (pt a) (pt b) (unitOn c)
  rig : LB.Gen (u.A.L.pull (eSec u.A.A))
  rig_gen : rig.IsGen
  fr : ∀ a, FrAt (pt a)
  fr_tors : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (pt a) (fr a)
  th : SecA u.A (PadicAlgCl p) 1
  th_val : ∀ a, ValAt th (pt a) (fr a) (y₀ ⟨S.th a, S.th_mem a⟩)
  s : S.J → SecA u.A (PadicAlgCl p) S.N
  ev_val : ∀ a i, ValAt (s i) (pt a) (fr a) (y₀ ⟨S.ev a i, S.ev_mem a i⟩)
  α : LB.Gen (LB.LinComb u.A.L (K := Fin 2) ![(snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A).left,
    (snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A ^ (ρ.n ^ ρ.k)).left] ![(S.N : ℤ), -((1 : ℕ) : ℤ)])
  α_gen : α.IsGen
  α_norm : LB.Gen.Corr u.A.L _ _ _ _ (LB.pullGen u.A.L _ _ α (ptSecT u.A.A 1).left)
    (rigT u.A.A u.A.L rig (TFK (R := u.V) (PadicAlgCl p)) ((S.N : ℤ) - 1))
  s_zero : IsTwistPull u.A.A u.A.L (mulT u.A.A _ (ρ.n ^ ρ.k)) (snd _ u.A.A ^ (ρ.n ^ ρ.k)) (lift_snd _ _)
    (S.N : ℤ) ((1 : ℕ) : ℤ) α th (s ρ.i₀)
  U : S.Gam → ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))
  U_sym : ∀ a, SymLift u.A.A u.A.L S.N S.N (pt (S.r • a)) (U a)
  U_act : ∀ a i σ, IsActOf u.A.A u.A.L S.N (U a) (s i) σ ↔ IsComb s (fun l => y₀ (algebraMap o S.R (S.ρ a l i))) σ

def NormVal {p : ℕ} [Fact p.Prime] (π : PadicAlgCl p) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) : Prop :=
  0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ (x : PadicAlgCl p) (q : ℚ), v x = (q : WithTop ℚ) ↔ ‖x‖ = ‖π‖ ^ (q : ℝ)
end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PreUniformisationComparisonTorusInvariantStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preUniformisation_comparison_torus_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D D' : DegPre R) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (U' : PreU I D' A' G) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _), IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL → ∀ (e : ℕ) (β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A), (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' → gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') = gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.P.L.ι) (jM' : D'.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.P.L.U jM' → gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = gw u y.left z jM (fun _ => jM') := by
  first | exact @GlobalTheory.preU_comparison_torus_invariant | exact GlobalTheory.preU_comparison_torus_invariant | (intros; apply GlobalTheory.preU_comparison_torus_invariant <;> assumption)
end

