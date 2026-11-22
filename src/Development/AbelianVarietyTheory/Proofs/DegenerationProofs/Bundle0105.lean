import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0103
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleAdaptedBasisLinkMatrix
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiRing

theorem basis_prod_famφT_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (U : Type) [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k, h (famφT D T 0 k) ^ DegPre.famε 1 k = h (snd T D.P.A).left := by
  have := D.P.isAb.comm
  rw [PsiExists.famφT_eq, PsiExists.cT_zero, _root_.mul_one]
  simp [Fin.prod_univ_four, DegPre.famε]

theorem exists_basis_fibNZ : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ th : SecBT D (𝟙_ _) 1 0, FibNZ (𝟙_ _ ⊗ D.P.A).hom th ∧ ∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b := by
  intro hT R _ _ _ D
  have := D.P.isAb.comm
  let T : Over (Spec (CommRingCat.of R)) := 𝟙_ _
  have e : translPt D.P.A (1 : T ⟶ D.P.A) = snd T D.P.A := by
    show (fst T D.P.A ≫ 1) * snd T D.P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P 1 le_rfl R (𝟙 _) (1 : T ⟶ D.P.A)
  change Fin (1 ^ D.P.g) → LB.Sec (twistLB D.P.A D.P.L 1 (1 : T ⟶ D.P.A)) at b
  change IsSecBasis (T := T) (A := D.P.A) _ b at hb
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have H : FormEq (K := Fin 2) ![(snd T D.P.A).left, (translPt D.P.A (1 : T ⟶ D.P.A)).left] ![((1 : ℕ) : ℤ) - 1, 1]
      (famφT D T 0) (DegPre.famε 1) := fun U _ h => by
    rw [basis_prod_famφT_zero, e]
    simp [Fin.prod_univ_two]
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB H (b i₀)
  have hf : (fst T D.P.A).left = (T ⊗ D.P.A).hom :=
    (Category.comp_id _).symm.trans (Over.w (fst T D.P.A))
  have key : ∀ g : SecBT D T 1 0, ∃ c : R, Mult D th g c := fun g => by
    obtain ⟨s, hs⟩ := exists_sec D.P.isLB (fun U _ h => (H U h).symm) g
    obtain ⟨c, hc, -⟩ := hb s
    have hc' := fun j => (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c i₀), fun Z r z J hJ => ?_⟩
    refine (hs Z r z J hJ).symm.trans (Eq.trans ?_ (congrArg _ (hth Z r z J hJ).symm))
    refine (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans ((gs_pull r (fst T D.P.A).left z ⊤ trivial _).trans ?_)) rfl))
    exact congrArg₂ (fun (q : Z ⟶ Spec (CommRingCat.of R)) (a : Γ(Spec (CommRingCat.of R), ⊤)) => gs q z ⊤ a)
      (congrArg (r ≫ ·) hf) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (c i₀)).symm
  refine ⟨th, fun y => ?_, key⟩
  have hp : IsPullback (snd T D.P.A).left (T ⊗ D.P.A).hom D.P.A.hom (𝟙 _) := by
    rw [← hf]
    exact (IsPullback.of_hasPullback T.hom D.P.A.hom).flip
  obtain ⟨t, ht⟩ := KeyPow.exists_sec_fibre_ne_zero hT D.P hp
  obtain ⟨z, hz, hz'⟩ := ht y
  obtain ⟨g, hg⟩ := exists_sec D.P.isLB (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    (φ' := famφT D T 0) (ε' := DegPre.famε 1) (fun U _ h => by
      rw [basis_prod_famφT_zero]; simp) t
  obtain ⟨c, hc⟩ := key g
  choose J hJ using fun χ : (T ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  refine ⟨z, hz, (MulPullSec.mem_nonzeroLocus_iff th (𝟙 _) z hJ).2 ?_⟩
  have u := (MulPullSec.mem_nonzeroLocus_iff (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    t (𝟙 _) z hJ).1 hz'
  rw [← hg _ _ z J hJ, hc _ _ z J hJ] at u
  exact isUnit_of_mul_isUnit_right u

end GlobalTheory.PsiRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoints_of_squareLevel_alt : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), 1 ≤ M → IsUnit (M : Γ(S, ⊤)) → ∀ lev : Out.Level P (M ^ 2) ze, ∃ pt : (Fin P.g ⊕ Fin P.g → ZMod M) → (baseOver S ⟶ P.A), (∀ a b, pt (a + b) = pt a * pt b) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ pt a = z) ∧ (∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd P.g M a b).val))) ∧ (∀ a, ∃ y : baseOver S ⟶ P.A, y ^ (M ^ 2) = 1 ∧ y ^ M = pt a) ∧ ∀ (i : Fin P.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → pt (Pi.single (.inl i) 1) = lev.pt i₁ ^ M ∧ pt (Pi.single (.inr i) 1) = lev.pt i₂ ^ M := by
  first | exact @GlobalTheory.exists_torsionPoints_of_squareLevel | exact GlobalTheory.exists_torsionPoints_of_squareLevel | (intros; apply GlobalTheory.exists_torsionPoints_of_squareLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwoGoodSectionsNearClosedPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.TwoSections

theorem exists_torsion_pair (M : Type) [CommGroup M] (P : M → Prop) (n : ℕ) (x : M)
    (h : ∀ c : M, 6 * Nat.card {h : M // h ^ n = 1 ∧ ¬ P (c * h)} < Nat.card {h : M // h ^ n = 1}) :
    ∃ b c : M, b ^ n = 1 ∧ c ^ n = 1 ∧ P b ∧ P c ∧ P (b * c) ∧ P (x * b) ∧ P (x * c) ∧ P (x * b * c) := by
  let H : Subgroup M := (powMonoidHom n : M →* M).ker
  have hH : Nat.card H = Nat.card {h : M // h ^ n = 1} := rfl
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by have := h 1; omega)
  have hB : ∀ c : M, 6 * Nat.card {h : H | ¬ P (c * h)} < Nat.card H := fun c => by
    have e : {h : H | ¬ P (c * h)} ≃ {h : M // h ^ n = 1 ∧ ¬ P (c * h)} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun h : M => h ^ n = 1) (fun h => ¬ P (c * h))
    rw [Nat.card_congr e, hH]
    exact h c
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.exists_pair_avoiding_small_sets H _ _ (hB 1) (hB x)
  simp only [Set.mem_ofPred_eq, not_not, _root_.one_mul, Subgroup.coe_mul] at h1 h2 h3 h4 h5 h6
  exact ⟨b, c, b.2, c.2, h1, h2, h3, h4, h5, by rwa [_root_.mul_assoc]⟩

theorem exists_pushHom {S S' X : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (q : X ⟶ S') (s : X ⟶ S) (e : q ≫ f = s) :
    ∃ ρ : (Over.mk q ⟶ G') →* (Over.mk s ⟶ G), ∀ c, (ρ c).left = c.left ≫ φ := by
  subst e
  exact ⟨pushHom h (Over.mk q), fun _ => rfl⟩

theorem exists_residue_point (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (w : X)
    (hw : IsClosed ({w} : Set X)) : ∃ (p : ℕ) (_ : Fact p.Prime) (x : Sp (kb p) ⟶ X), ∀ s, x s = w := by
  have := (GlobalTheory.jacobson_closedPoints_tools_int X π).2.1 w hw
  obtain ⟨p, hp⟩ := CharP.exists (X.residueField w)
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime (X.residueField w) p⟩
  have : CharP (kb p) p := charP_kb
  have : IsAlgClosed (kb p) := isAlgClosed_kb
  letI : Algebra (ZMod p) (X.residueField w) := ZMod.algebra _ p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) (X.residueField w) := Module.Finite.of_finite
  let r : X.residueField w →+* kb p := (IsAlgClosed.lift (R := ZMod p) (S := X.residueField w) (M := kb p)).toRingHom
  refine ⟨p, hpp, Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w, fun s => ?_⟩
  have : (Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w) s ∈ Set.range (X.fromSpecResidueField w) :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [Scheme.range_fromSpecResidueField] at this

end GlobalTheory.ZJ.TwoSections

namespace GlobalTheory.ZJ
open TwoSections

theorem Core.Law.six_of_few : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), C.HasTests → T.BTest L → C.TorsSec n → T.Few n → L.CompanionTheory (T.Om L) := by
  intro hext C L T n hT hB hS hF w hw
  letI := L.grp
  letI := L.comm
  have := C.lft
  have := C.flat
  have hlft : LocallyOfFiniteType C.GG.hom := (GlobalTheory.ZJ.core_basic C).2.1
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨p, hp, x, hx⟩ := @exists_residue_point C.G.toScheme (C.GG.hom ≫ C.π) hlft' w hw
  obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
  obtain ⟨y, hy, hyU⟩ := hlift (x ≫ C.GG.hom)
  obtain ⟨τ⟩ := hT p y hyU
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_thetaExtension_test hext C T p y τ fun p _ y τ => (L.test p y τ).1
  let s₀ : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  have hs : ∀ s : Sp (kb p), s = s₀ := fun s => Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
  have hr : rPt p s₀ = cPt p := IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  have hz : y (cPt p) = (x ≫ C.GG.hom) s₀ := by rw [← hy, Scheme.Hom.comp_apply, hr]
  obtain ⟨N, hN, hsec⟩ := hS _ (hcl (x ≫ C.GG.hom) s₀)
  have hrange : Set.range (x ≫ C.GG.hom) ⊆ Set.range N.ι := by
    rintro _ ⟨s, rfl⟩
    rw [hs s, Scheme.Opens.range_ι]
    exact hN
  let t : Sp (kb p) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (x ≫ C.GG.hom) hrange
  have ht : t ≫ N.ι = x ≫ C.GG.hom := IsOpenImmersion.lift_fac _ _ _
  have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = t ≫ N.ι := by rw [Category.assoc, τ.fac, hy, ht]
  have hpb := (L.test p y τ).1
  let c₀ : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H :=
    Over.homMk (hpb.lift x (rPt p ≫ spMap τ.j) (ht.symm.trans e.symm)) (hpb.lift_snd _ _ _)
  have hc₀ : c₀.left ≫ τ.f = x := hpb.lift_fst _ _ _
  obtain ⟨ρ, hρ⟩ := exists_pushHom (L.test p y τ) _ _ e
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := exists_torsion_pair (Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H)
    (fun c => ⊤ ≤ c.left ⁻¹ᵁ Out.nonzeroLocus E.θ) n c₀ (hF p y τ E)
  obtain ⟨b₁, hb₁, hb₂⟩ := hsec p y τ t b hz (ht.trans hy.symm) hb
  obtain ⟨c₁, hc₁, hc₂⟩ := hsec p y τ t c hz (ht.trans hy.symm) hc
  have key : ∀ d : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H, ⊤ ≤ d.left ⁻¹ᵁ Out.nonzeroLocus E.θ →
      Set.range (ρ d).left ⊆ T.Om L := by
    rintro d hd _ ⟨s, rfl⟩
    have := τ.j_loc
    have h0 : τ.H.hom (d.left s) = IsLocalRing.closedPoint τ.V := by
      rw [← Scheme.Hom.comp_apply, Over.w d, hs s]
      exact (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (spMap τ.j) hr).trans (IsLocalRing.comap_closedPoint τ.j))
    rw [hρ]
    exact (Scheme.Hom.comp_apply _ _ _).symm ▸ (hB p y τ E _ h0).2 (hd trivial)
  refine ⟨N, Over.homMk b₁ hb₁, Over.homMk c₁ hc₁, kb p, inferInstance, t, ρ c₀, ρ b, ρ c, ?_,
    (hρ b).trans hb₂.symm, (hρ c).trans hc₂.symm, ?_⟩
  · rw [hρ, hc₀]
    ext v
    exact ⟨fun ⟨s, h⟩ => h ▸ hx s, fun h => ⟨s₀, (hx _).trans h.symm⟩⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false, ← map_mul] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [key _ h1, key _ h2, key _ h3, key _ h4, key _ h5, key _ h6]

end GlobalTheory.ZJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBaseStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_expansion_section_admissible_base : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k), ∃! f : ∀ α, SecBT D (𝟙_ _) k α, U.ExpT (𝟙_ _) k σ f := by
  first | exact @GlobalTheory.CompleteBaseExpansion.main | exact GlobalTheory.CompleteBaseExpansion.main | (intros; apply GlobalTheory.CompleteBaseExpansion.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitGeneratingSectionPullbackField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenSecField

open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR

theorem flat_of_injective {R K : Type} [CommRing R] [IsDomain R] [Field K] {φ : R →+* K}
    (hφ : Function.Injective φ) : φ.Flat := by
  have e : φ = (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap hφ x).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  · let _ := (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).toAlgebra
    exact (inferInstance : Module.Flat (FractionRing R) K)

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem exists_pow_one (u : LB.Sec L) : ∃ s : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
    sval s r z J = gs r z _ (u.f (J r)) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (u.f (j 0)), fun j j' => fn_ext fun y hy => ?_⟩,
    fun Z r z J hJ => ?_⟩
  · refine (gs_res (𝟙 X) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2)))
      (gs_res (𝟙 X) y _ hy _))).symm)
    refine (gs_res (𝟙 X) y (le j) hy.1 _).trans ((FlatSec.gs_sec_trans u (𝟙 X) y (le j hy.1) (le j' hy.2)).trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 X) y (le j') hy.2 _).symm))
    simp
  · rw [sval_of _ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact gs_res r z (le fun _ => J r) (Set.mem_iInter.2 fun _ => hJ r) _

theorem cst_zero' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  rw [cst, map_zero, gs_eq q z ⊤ trivial, map_zero, map_zero]

theorem sval_eq_zero {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] {f : X ⟶ Sp R} {π : X' ⟶ X} {f' : X' ⟶ Sp R'}
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull π)} (hw : w.IsGen) {th : H0 L 1} (hth : ∀ s : H0 L 1, ∃ a, SecIsMul f a s th)
    (h₀ : ∀ y J, Good L y J → sval th π y J = 0) (s : H0 L' 1) (y : X') {J'} (hJ' : Good L' y J') :
    sval s (𝟙 X') y J' = 0 := by
  obtain ⟨t, ht⟩ := exists_sec hL' (φ' := fun _ : PUnit => 𝟙 X') (ε' := fun _ => 1)
    (fun U _ h => by simp) s
  obtain ⟨σ, hσ⟩ := ArcPull.exists_up_sec ((isGen_iff w).1 hw) hL hL' (fun _ : PUnit => 𝟙 X') (fun _ => π)
    (fun _ => 1) (𝟙 X') (fun _ => by simp) t
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H L hL σ
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have e := hσ _ (𝟙 X') y J J' hJ hJ'
  rw [ht _ _ y J' hJ', sval_of σ _ y J (fun _ => J π) (fun _ => by rw [Category.id_comp]), Category.id_comp] at e
  have z : ∀ i, gs π y _ ((u i).f (J π)) = 0 := fun i => by
    obtain ⟨v, hv⟩ := exists_pow_one (u i)
    obtain ⟨a, ha⟩ := hth v
    rw [← hv _ π y J hJ, sval_of_secIsMul ha π y hJ, h₀ y J hJ, mul_zero]
  have e' := (hu y (J π) (hJ π)).symm.trans e
  simp only [z, mul_zero, Finset.sum_const_zero] at e'
  exact (Units.mul_right_eq_zero _).1 e'.symm

end GlobalTheory.GenSecField

namespace GlobalTheory

open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.GenSecField in

theorem exists_unit_generating_section_pull : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (th : H0 D.P.L 1) (th' : H0 D'.P.L 1), (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D'.P.L 1, ∃ r : K, ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → ∃ c : Kˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval th (r ≫ PsiEvenPull.proj hD) z J = (TauTwist.unitAt (r ≫ D'.P.A.hom) z c * ArcPull.om hD.w z J J' r).val * sval th' r z J' := by
  intro R K _ _ _ φ hφ D D' hD th th' hth hth'
  have hc : ∀ _ : Fin 1, 𝟙 D'.P.A.left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ 𝟙 D.P.A.left :=
    fun _ => (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L _ D.P.isLB D'.P.isLB hD.w hD.w_gen (Fin 1)
    (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)) (PsiEvenPull.proj hD) hc th
  obtain ⟨c, hac⟩ := hth' a
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      sval th (r ≫ PsiEvenPull.proj hD) z J =
        cst (r ≫ D'.P.A.hom) z c * (ArcPull.om hD.w z J J' r).val * sval th' r z J' := fun Z r z J J' hJ hJ' => by
    have e := FamFieldPull.IsSecPull.val ha hc r z hJ hJ'
    rw [sval_of_secIsMul (p := D'.P.A.hom) hac r z hJ', Fin.prod_univ_one, Category.comp_id, zpow_natCast,
      pow_one] at e
    exact e.trans ((mul_left_comm _ _ _).trans (_root_.mul_assoc _ _ _).symm)
  by_cases h : c = 0
  · subst h
    have : IsProper D.P.A.hom := D.P.isAb.proper
    have : CompactSpace D.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.P.A.hom
    have : QuasiSeparatedSpace D.P.A.left := quasiSeparatedSpace_of_quasiSeparated D.P.A.hom
    have h₀ : SecIsMul D'.P.A.hom (0 : K) th' th' := secIsMul_of_sval D'.P.isLB fun y J' hJ' => by
      rw [cst_zero', zero_mul]
      refine sval_eq_zero (flat_of_injective hφ) (pull_grp hD).1 D.P.isLB D'.P.isLB hD.w_gen hth
        (fun x J hJ => ?_) th' y hJ'
      obtain ⟨I, hI⟩ := DegPull.exists_good' D'.P.isLB x
      have e := key _ (𝟙 _) x J I hJ hI
      rwa [Category.id_comp, cst_zero', zero_mul, zero_mul] at e
    refine ⟨1, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', sval_of_secIsMul h₀ r z hJ', cst_zero', zero_mul, zero_mul, zero_mul, mul_zero]
  · refine ⟨Units.mk0 c h, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', Units.val_mul, TauTwist.unitAt_val]
    rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormVanishesOfTorsionTorusExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TorsionVanish

theorem form_vanishes_of_torsion : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ v, Crd (Φ.H 1) F x.left v ∧ MvPolynomial.eval v Pf = 0) → ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, MvPolynomial.eval v Pf = 0) := by
  intro L1 L2 k _ _ Φ g N N' q J _ cls F π hBig hGood hg hN' d Pf hd hPf hx v hv
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · obtain ⟨v0, -, hv0⟩ := hx 1 (one_pow _)
    have hC : Pf = MvPolynomial.C (Pf.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hPf.totalDegree_le)
    rw [hC] at hv0 ⊢
    simpa using hv0
  obtain ⟨φ, -, hsupp, hval⟩ := GlobalTheory.ZH.FormSec.exists_formSec k Φ J F d Pf hPf
  obtain ⟨hpart, hfin, -, hsum⟩ := GlobalTheory.ZH.WtPart.weight_parts k Φ d
  obtain ⟨-, -, hsep⟩ := GlobalTheory.exists_basis_unique_min_and_sums_separated Φ.E.X q hGood.pos _ g N N'
    (N ^ g * g.factorial) rfl (by omega) hBig.lll hBig.sep
  have hdist : ∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + N' • w) → α = β := by
    rintro α hα β hβ ⟨w, hw⟩
    obtain ⟨a, ha, rfl⟩ := hsupp α hα
    obtain ⟨b, hb, rfl⟩ := hsupp β hβ
    have h0 : w = 0 := hsep d a b hd
      (fun j => by obtain ⟨i, hi⟩ := ha j; exact (hGood.supp i _ hi).1)
      (fun j => by obtain ⟨i, hi⟩ := hb j; exact (hGood.supp i _ hi).1) w hw
    rw [hw, h0, smul_zero, add_zero]
  have htor : ∀ x : Φ.Pt, x ^ N' = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ := fun x hx1 => by
    obtain ⟨v0, hc, h0⟩ := hx x hx1
    exact (hval x v0 hc).1 h0
  choose ψ hψ using hpart φ
  have hψ0 : ∀ α l, (ψ α).f l = 0 := fun α =>
    GlobalTheory.PureZero.pure_eq_zero_of_vanishing_on_torsion L1 L2 k Φ g N N' d π hBig hN' (by omega) hd1 hd α (ψ α) (hψ α).1
      (GlobalTheory.T.part_vanishes_on_torus_torsion_fourier k Φ d N' hN' φ hdist htor α (ψ α) (hψ α))
  have hφ0 : ∀ l, φ.f l = 0 := fun l => by
    rw [hsum φ (hfin φ).toFinset ψ (by simp) (fun α _ => hψ α) l]
    exact Finset.sum_eq_zero fun α _ => hψ0 α l
  obtain ⟨x, hxp, hc⟩ := hv
  refine (hval (Over.homMk x hxp) v hc).2 fun h => ?_
  have hb : Out.nonzeroLocus φ = ⊥ := by
    simp [Out.nonzeroLocus, hφ0]
  rw [hb] at h
  obtain ⟨p⟩ : Nonempty (Sp k) := (inferInstance : Nonempty (PrimeSpectrum k))
  exact h (Set.mem_univ p)

end GlobalTheory.ZH.TorsionVanish
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.immBy_weight_zero' : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → ImmBy Φ.G.hom (Φ.H 1) F {i | cls i = 0}) := by
  first | exact @GlobalTheory.ZH.ClosedImm.immBy_weight_zero | exact GlobalTheory.ZH.ClosedImm.immBy_weight_zero | (intros; apply GlobalTheory.ZH.ClosedImm.immBy_weight_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFiniteKerOfSurjPointsSameDimensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_ker_of_surj_points_same_dimension : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ), SmConn G → SmConn G' → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g G'.hom → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  first | exact @GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq | exact GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq | (intros; apply GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.FibreIndep

open GlobalTheory.VVRank GlobalTheory.UnivBasisMove

theorem linearIndependent_pullM (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n)
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (p : T'.left) (hp : ∀ q, q = p) (h : T' ⟶ T)
    {J : Type} [Fintype J] (hJ : Fintype.card J = n ^ P.g) (s : J → SecM P.A P.L n T)
    (hs : ∀ x, ∃ c : J → Γ(T.left, ⊤), x = ∑ i, c i • s i) :
    LinearIndependent Γ(T'.left, ⊤) (fun i => pullM P.A P.L n h (s i)) := by
  have hne : Nonempty (⊤ : T'.left.Opens) := ⟨⟨p, trivial⟩⟩
  have hnt : Nontrivial Γ(T'.left, ⊤) := Scheme.component_nontrivial T'.left ⊤
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn (T'.hom p)
  let l : T' ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι T'.hom (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [hp y]
      exact hV)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  obtain ⟨c, -⟩ := exists_basis P n b hb T' l
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis c
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (fun x _ => ?_)
    (by rw [Module.finrank_eq_card_basis c, Fintype.card_fin, hJ])
  refine Submodule.span_le.2 ?_ (LinkMatrix.mem_span_pullM hS P n hn p hp h x)
  rintro _ ⟨u, rfl⟩
  obtain ⟨a, rfl⟩ := hs u
  rw [map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem linearIndependent_moved : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → LinearIndependent Γ((TFK (R := u.V) (PadicAlgCl p)).left, ⊤) (fun i => SecM.ofSec u.A.A (t i)) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u w hw t ht
  have hN : 1 ≤ S.N := by
    rw [ρ.N_eq]
    exact Nat.one_le_pow _ _ (pow_pos ρ.n_prime.pos _)
  let T := TFK (R := u.V) (PadicAlgCl p)
  let T' : Over (Sp S.R) := Over.mk (T.hom ≫ spMap u.yK)
  have : IsAffine T'.left := inferInstanceAs (IsAffine (Sp (PadicAlgCl p)))
  have : IsAffine (baseOver (Sp S.R)).left := inferInstanceAs (IsAffine (Sp S.R))
  let h₀ : T' ⟶ baseOver (Sp S.R) := Over.homMk (spMap y₀) (base_eq u)
  have li := linearIndependent_pullM hL.2.1.secBaseChangeAny ρ.P S.N hN (T' := T')
    (IsLocalRing.closedPoint (PadicAlgCl p))
    (fun q => Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _) h₀ (J := S.J)
    (by rw [ρ.g_eq]; exact ρ.card) (fun i => SecM.ofSec ρ.P.A (ρ.s i)) (fun x => by
      obtain ⟨c, hc⟩ := (ρ.s_basis (SecM.toSec ρ.P.A x)).exists
      refine ⟨c, Subtype.ext (funext fun j => ?_)⟩
      rw [Submodule.coe_sum, Finset.sum_apply]
      exact hc j)
  obtain ⟨E, hE⟩ := exists_linearEquiv u.cart hw ρ.P.isLB u.A.isLB (S.N : ℤ) T
  have e : ∀ i, E (pullM ρ.P.A ρ.P.L S.N h₀ (SecM.ofSec ρ.P.A (ρ.s i))) = SecM.ofSec u.A.A (t i) := fun i => by
    have r : Rel u.cart (T := T) (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) w (SecM.ofSec u.A.A (t i))
      (SecM.ofSec ρ.P.A (ρ.s i)) := ht i
    have r' := r.pull (T' := T) (T₀' := T') (𝟙 T.left) (Category.id_comp _) (𝟙 T) h₀ rfl
    rw [pullM_id _ u.A.isLB] at r'
    exact (hE _).unique_down ρ.P.isLB u.A.isLB r'
  have li' := LinearIndependent.map' (R := Γ(T.left, ⊤)) li E.toLinearMap E.ker
  exact (funext e : _ = fun i => SecM.ofSec u.A.A (t i)) ▸ li'

end GlobalTheory.ZH.FibreIndep
end
end

