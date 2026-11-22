import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesTorsion
open IsLocalRing GlobalTheory.UT.ExactTerm

theorem nonempty_equiv_of_basis {G : Type} [CommGroup G] {k r : ℕ} (hk : k ≠ 0) (v : Fin r → G) (hv : ∀ i, v i ^ k = 1)
    (h : ∀ y : G, y ^ k = 1 → ∃! c : Fin r → ZMod k, (List.ofFn fun i => v i ^ (c i).val).prod = y) :
    Nonempty ((powMonoidHom k : G →* G).ker ≃* Multiplicative (Fin r → ZMod k)) := by
  have : NeZero k := ⟨hk⟩
  simp only [List.prod_ofFn] at h
  let f : Multiplicative (Fin r → ZMod k) →* (powMonoidHom k : G →* G).ker := MonoidHom.mk'
    (fun c => ⟨∏ i, v i ^ (c.toAdd i).val, by
      show (∏ i, v i ^ (c.toAdd i).val) ^ k = 1
      rw [← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]⟩)
    fun a b => Subtype.ext (by
      show ∏ i, v i ^ (a.toAdd i + b.toAdd i).val = (∏ i, v i ^ (a.toAdd i).val) * ∏ i, v i ^ (b.toAdd i).val
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add])
  refine ⟨(MulEquiv.ofBijective f ⟨fun a b e => ?_, fun y => ?_⟩).symm⟩
  · exact (h _ (f b).2).unique (congrArg Subtype.val e) rfl
  · obtain ⟨c, hc⟩ := (h y.1 y.2).exists
    exact ⟨Multiplicative.ofAdd c, Subtype.ext hc⟩

section Geom
variable (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
  (t : Sp K ⟶ S)
include hL

theorem exists_pow_eq (a : Over.mk t ⟶ P.A) {n : ℕ} (hn : 1 ≤ n) : ∃ b : Over.mk t ⟶ P.A, b ^ n = a := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hL.mulN S P n hn
  obtain ⟨s, hs⟩ := H1.SectionDivision.exists_section (k := K) (pullback.snd (mulA P.A n).left a.left)
  have hb : (s ≫ pullback.fst (mulA P.A n).left a.left) ≫ (mulA P.A n).left = a.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs]; exact Category.id_comp _
  have hw : (s ≫ pullback.fst (mulA P.A n).left a.left) ≫ P.A.hom = t := by
    rw [← Over.w (mulA P.A n), ← Category.assoc, hb]; exact Over.w a
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ n = b ≫ mulA P.A n := fun b =>
    (congrArg (· ^ n) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) n b).symm
  rw [e]
  exact Over.OverMorphism.ext hb

theorem exists_basis {k : ℕ} (hk : (k : K) ≠ 0) : ∃ v : Fin (2 * P.g) → (Over.mk t ⟶ P.A), (∀ i, v i ^ k = 1) ∧
    ∀ y : Over.mk t ⟶ P.A, y ^ k = 1 →
      ∃! c : Fin (2 * P.g) → ZMod k, (List.ofFn fun i => v i ^ (c i).val).prod = y := by
  have := P.isAb.comm
  let c : Γ(Sp K, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(Sp K, ⊤) := c.toMulEquiv.isDomain _
  have hk0 : k ≠ 0 := fun e => hk (by rw [e, Nat.cast_zero])
  have : NeZero (k : K) := ⟨hk⟩
  have : NeZero k := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K k
  have hζ' : IsPrimitiveRoot (c.symm ζ) k := hζ.map_of_injective c.symm.injective
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P k (Over.mk t)
  exact PrincipalNumerics.exists_basis_of_pairing (G := Over.mk t ⟶ P.A) (g := P.g) (Nat.pos_of_ne_zero hk0)
    (fun d hd => (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hk0))).2.2.2.2 K t (by
      obtain ⟨e, rfl⟩ := hd
      rw [Nat.cast_mul] at hk
      exact left_ne_zero_of_mul hk))
    (hζ'.isUnit_unit hk0) (fun x y c => WeilIs P.A P.L k x y c) w₁ w₂ w₃
    (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) (ThetaRep.eq_one_of_weilIs hL P t hk)
end Geom

section Val
variable {C : Type} [NormedField C] (S : ValuationSubring C)

theorem affine_ext {R : Type} [CommRing R] {f g : Sp S ⟶ Sp R} (h : spMap S.subtype ≫ f = spMap S.subtype ≫ g) :
    f = g := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) f
  obtain ⟨b, rfl⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) g
  have e₁ : a ≫ CommRingCat.ofHom S.subtype = b ≫ CommRingCat.ofHom S.subtype :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_comp]; exact h)
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
    (RingHom.congr_fun (congrArg CommRingCat.Hom.hom e₁) x)))

theorem separated_ext {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) [IsSeparated p] {f g : Sp S ⟶ X}
    (h : spMap S.subtype ≫ f = spMap S.subtype ≫ g) : f = g := by
  have e : f ≫ p = g ≫ p := affine_ext S (by rw [← Category.assoc, h, Category.assoc])
  let Q : ValuativeCommSq p :=
    { R := S, K := C, i₁ := spMap S.subtype ≫ f, i₂ := f ≫ p, commSq := ⟨Category.assoc _ _ _⟩ }
  exact congrArg CommSq.LiftStruct.l ((IsSeparated.valuativeCriterion p Q).elim ⟨f, rfl, rfl⟩ ⟨g, h.symm, e.symm⟩)

variable {S} (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1)
include hS

theorem norm_valF {X : Scheme.{0}} (x : Sp S ⟶ X) (U : X.Opens) (a : Γ(X, U))
    (ha : x (closedPoint S) ∈ X.basicOpen a) : ‖valF (spMap S.subtype ≫ x) U a‖ = 1 := by
  have h₁ : x ⁻¹ᵁ X.basicOpen a = ⊤ := DVR.eq_top_of_closedPoint_mem _ ha
  have ht : ⊤ ≤ x ⁻¹ᵁ U := fun q _ => X.basicOpen_le a (h₁.ge (Set.mem_univ q))
  have h' : ⊤ ≤ (spMap S.subtype ≫ x) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap S.subtype q))
  have hu : IsUnit ((x.appLE U ⊤ ht).hom a) := by
    refine (Sp S).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ((Sp S).mem_basicOpen _ y hy).1 ?_
    rw [Scheme.basicOpen_appLE, h₁]
    exact ⟨trivial, trivial⟩
  obtain ⟨u, hu⟩ := hu.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
  have e : (spMap S.subtype ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      x.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) x U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  have e' : valF (spMap S.subtype ≫ x) U a = S.subtype u.val := by
    rw [valF, dif_pos h', hu]
    exact congrArg (fun g => g.hom a) e
  have m : ‖S.subtype u.val‖ * ‖S.subtype u.inv‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    exact (congrArg (fun q => ‖S.subtype q‖) u.val_inv).trans (by rw [map_one, norm_one])
  have b₁ : ‖S.subtype u.val‖ ≤ 1 := (hS _).1 (show S from u.val).2
  have b₂ : ‖S.subtype u.inv‖ ≤ 1 := (hS _).1 (show S from u.inv).2
  rw [e']
  nlinarith [norm_nonneg (S.subtype u.val), norm_nonneg (S.subtype u.inv)]

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (m : Sp S ⟶ Y)
  {J : (Sp C ⟶ X) → L.ι} (hm : ∀ k, ⊤ ≤ (m ≫ φ k) ⁻¹ᵁ L.U (J ((spMap S.subtype ≫ m) ≫ φ k)))
include hm

theorem norm_vF (t : LB.Gen (LB.LinComb L φ ε)) : ‖vF t (spMap S.subtype ≫ m) J‖ = 1 := by
  refine norm_valF hS m _ _ ?_
  exact (Scheme.basicOpen_of_isUnit Y (Units.isUnit _)).ge (Set.mem_iInter.2 fun k => hm k trivial)

theorem norm_sF (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ z J', Good L z J' → IsUnit (sval s (Spec.map (CommRingCat.ofHom (residue S)) ≫ m) z J')) :
    ‖sF s (spMap S.subtype ≫ m) J‖ = 1 := by
  let z : Spec (CommRingCat.of (ResidueField S)) := closedPoint (ResidueField S)
  obtain ⟨J', hJ'⟩ := GlobalTheory.UT.CoefBasic.exists_good' hL z
  have e : (Spec.map (CommRingCat.ofHom (residue S)) ≫ m) z = m (closedPoint S) :=
    congrArg m (IsLocalRing.comap_closedPoint (residue S))
  have h₁ : (Spec.map (CommRingCat.ofHom (residue S)) ≫ m) z ∈
      LB.wchart L φ fun k => J ((spMap S.subtype ≫ m) ≫ φ k) := by
    rw [e]
    exact Set.mem_iInter.2 fun k => hm k trivial
  have h₂ := (congrArg IsUnit (sec_trans s _ z (hJ'.mem φ _) h₁)).mp (h z J' hJ')
  refine norm_valF hS m _ _ ?_
  rw [← e]
  exact (isUnit_gs_iff _ z _ h₁ _).1 (isUnit_of_mul_isUnit_right h₂)
end Val

theorem exists_norm_th (hL : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {D : DegPre R} {C : Type} [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (hR : CExt R ⊥ C)
    {N : NumD C} (ν : NumOf D C N) (hν : ν.IntN) {n : ℕ} (hn : 2 ≤ n) (hC : ‖(n : C)‖ = 1) (a : N.A) :
    ∃ t, t ^ n = 1 ∧ ‖N.th (a * t)‖ = 1 := by
  obtain ⟨S, hS, hI⟩ := hν
  have := D.P.isAb.proper
  let f : R →+* S := ((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S fun r => (hS _).2 (hR.1 r)
  have hf : spMap S.subtype ≫ spMap f = (TF (R := R) C).hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  let ρ : TF (R := R) C ⟶ Over.mk (spMap f) := Over.homMk (spMap S.subtype) hf
  have hJ : ∀ y : Sp S ⟶ D.P.A.left, y ≫ D.P.A.hom = spMap f →
      ⊤ ≤ y ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ y)) := fun y hy => by
    obtain ⟨x₀, e, h⟩ := hI (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy]; exact hf))
    obtain rfl : x₀ = y := separated_ext S D.P.A.hom e
    exact h
  obtain ⟨m₀, hm₀, -⟩ := hI (ν.eA a)
  let m : Over.mk (spMap f) ⟶ D.P.A := Over.homMk m₀ (affine_ext S (by
    rw [← Category.assoc, hm₀]; exact (Over.w (ν.eA a)).trans hf.symm))
  have hm : ρ ≫ m = ν.eA a := Over.OverMorphism.ext hm₀
  have : IsAlgClosed (ResidueField S) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed S C
  have hκ : (n : ResidueField S) ≠ 0 := by
    have h0 : (n : C) ≠ 0 := fun e => by simp [e] at hC
    have hu : IsUnit (n : S) := IsUnit.of_mul_eq_one (⟨(n : C)⁻¹, (hS _).2 (by simp [hC])⟩ : S)
      (Subtype.ext (by simp [h0]))
    have := (hu.map (residue S)).ne_zero
    rwa [map_natCast] at this
  let r : Over.mk (Spec.map (CommRingCat.ofHom (residue S)) ≫ spMap f) ⟶ Over.mk (spMap f) := Over.homMk _ rfl
  obtain ⟨β, -, hβ⟩ := exists_generator_ne_zero hL.secBaseChange D.P
  obtain ⟨th, h₀, hth⟩ := hβ (ResidueField S) (Spec.map (CommRingCat.ofHom (residue S)) ≫ spMap f)
  obtain ⟨x₀, hx₀, hu⟩ := exists_good_point hL.goodPt hL.polBaseChange D.P _ hn hκ th h₀ (r ≫ m)
  obtain ⟨hfin, hflat, -⟩ := hL.mulN _ D.P n (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : Over.mk (spMap f) ⟶ D.P.A, x ^ n = 1 ∧
      Spec.map (CommRingCat.ofHom (residue S)) ≫ x.left = x₀.left :=
    exists_torsion_lift S D.P.A n (spMap f) x₀ hx₀
  have ex' : r ≫ x = x₀ := Over.OverMorphism.ext ex
  obtain ⟨c, hc⟩ := ν.th_gen β
  refine ⟨ν.eA.symm (ρ ≫ x), by rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one], ?_⟩
  have e : (ν.eA (a * ν.eA.symm (ρ ≫ x))).left = spMap S.subtype ≫ (m * x).left := by
    rw [map_mul, MulEquiv.apply_symm_apply, ← hm, ← MonObj.comp_mul]; rfl
  have h₁ : ‖sF ν.th (spMap S.subtype ≫ (m * x).left) ν.J‖ = 1 :=
    norm_sF hS (m * x).left (fun _ => by
      simpa only [Category.comp_id] using hJ (m * x).left (Over.w _)) D.P.isLB ν.th fun z J hz => by
      have q := hu z J hz
      rw [hth _ _ z J hz, ThetaPtMove.ptSecT_snd, ← ex', ← MonObj.comp_mul] at q
      exact isUnit_of_mul_isUnit_right ((congrArg IsUnit
        (IndivisibleSection.sval_of_secIsMul (s := β) (t := ν.th) hc _ z hz)).mp q)
  have h₂ : ‖vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
      (spMap S.subtype ≫ spMap f) ν.J‖ = 1 :=
    norm_vF hS (spMap f) (fun _ => by
      rw [Category.assoc]
      exact hJ _ (Over.w (1 : Over.mk (spMap f) ⟶ D.P.A))) _
  have h₃ := congrArg norm (ν.th_eq (a * ν.eA.symm (ρ ≫ x)))
  rw [norm_mul, e, h₁, ← hf, h₂, _root_.mul_one] at h₃
  exact h₃

theorem tors_of_integral : Laws → Laws2 → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing R) C], CExt R ⊥ C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ n : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n D.P.g := by
  intro hL _ hB R _ _ _ _ D he hb C _ _ _ _ hR N ν hν n hp ho hC
  have h0 : (n : C) ≠ 0 := fun e => by simp [e] at hC
  have hj : ∀ j : ℕ, ((n ^ j : ℕ) : C) ≠ 0 := fun j => by rw [Nat.cast_pow]; exact pow_ne_zero _ h0
  obtain ⟨hW, hU⟩ := hB R D he hb C N ν
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  refine ⟨fun x => ?_, fun j => ?_, fun j b hb h => ?_, exists_norm_th hL hR ν hν hp.two_le hC, fun j h1 x x' l hl h => ?_⟩
  · obtain ⟨y, hy⟩ := exists_pow_eq hL D.P (jFK (R := R) C ≫ jK R) (ν.eA x) hp.pos
    exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  · obtain ⟨v, hv, h⟩ := exists_basis hL D.P (jFK (R := R) C ≫ jK R) (hj j)
    refine nonempty_equiv_of_basis (pow_ne_zero j hp.ne_zero) (fun i => ν.eA.symm (v i))
      (fun i => by rw [← map_pow, hv, map_one]) fun y hy => ?_
    refine (existsUnique_congr fun c => ?_).1 (h (ν.eA y) ((tor _ _).2 hy))
    simp only [List.prod_ofFn, ← map_pow, ← map_prod, MulEquiv.symm_apply_eq]
  · refine ν.eA.map_eq_one_iff.1 (ThetaRep.eq_one_of_weilIs hL D.P (jFK (R := R) C ≫ jK R) (hj j) _
      ((tor _ _).2 hb) fun y hy => ?_)
    obtain ⟨b', rfl⟩ := ν.eA.surjective y
    have hb' := (tor _ _).1 hy
    have := hW (n ^ j) (Nat.pos_of_ne_zero (pow_ne_zero j hp.ne_zero)) b b' hb hb'
    rwa [h b' hb', show unitOn (1 : Cˣ) = 1 from map_one (Units.map _)] at this
  · obtain ⟨-, hc⟩ := hU (n ^ j) ho.pow (hj j) {b : N.A // b ^ (n ^ j) ^ 2 = 1} Subtype.val Subtype.property
    obtain ⟨-, hs, -, hsep⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C _ D.P (jFK (R := R) C ≫ jK R) (n ^ j) ho.pow (hj j)
      {b : N.A // b ^ (n ^ j) ^ 2 = 1} (fun i => ν.eA i.1) fun i => (tor _ _).2 i.2
    have h3 : 3 ≤ n ^ j := by
      have : 3 ≤ n := by
        have := hp.two_le
        obtain ⟨k, rfl⟩ := ho
        omega
      exact this.trans (Nat.le_self_pow (by omega) n)
    refine ν.eA.injective (hsep h3 (fun y hy => ?_) _ _ (fun i => N.uth (n ^ j) i.1 x) (hc x)
      ((hs _ (fun i => N.uth (n ^ j) i.1 x') _ (hc x')).2 ⟨Units.mk0 l hl, funext fun i => h i.1 i.2⟩)).1
    obtain ⟨b, rfl⟩ := ν.eA.surjective y
    exact ⟨⟨b, (tor _ _).1 hy⟩, rfl⟩

end GlobalTheory.ValuesTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem surjective_mulN_of_isAbelianScheme (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) (n : ℕ) (hn : (n : K) ≠ 0) : Surjective (mulN B n).left := by
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have hft : LocallyOfFiniteType B.hom := inferInstance
  have : Flat (mulN B n).left :=
    MulEtaleDvr.flat_mulN_field K B n (isUnit_iff_ne_zero.2 hn) hft
  have : IsProper ((mulN B n).left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper (mulN B n).left := IsProper.of_comp _ B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : LocallyOfFinitePresentation (mulN B n).left := inferInstance
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  have hc : IsClopen (Set.range (mulN B n).left) :=
    ⟨(mulN B n).left.isClosedMap.isClosed_range, (mulN B n).left.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))⟩

theorem abelian_torsion_finite_and_mulN_surjective :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) :=
  ⟨AbTorsionFinite.finite_torsion,
    fun K _ _ B _ hB n hn => surjective_mulN_of_isAbelianScheme K B hB n hn⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionAbelianVarietyLeConstMulPowStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_abelianVariety_le_const_mul_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ a, SmoothOfRelativeDimension a B.hom → ∃ C : ℕ, ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ≤ C * n ^ (2 * a) := by
  first | exact @GlobalTheory.SS.card_torsion_le | exact GlobalTheory.SS.card_torsion_le | (intros; apply GlobalTheory.SS.card_torsion_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_sections_thickenings_localRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → (∀ e, IsProjBy (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (K : Type) [Field K] (g₀ : R ⧸ I ^ (0 + 1) →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ (Y 0).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)) → ∀ (N₀ : LB X₀) (w₀ : LB.Iso N₀ ((N 0).pull π)), N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ s₀ : LB.Sec (N 0), ∃ s : ∀ e, LB.Sec (N e), s 0 = s₀ ∧ ∀ e, (∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' → gs (β e) z _ ((s (e + 1)).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e).f k')) := by
  first | exact @GlobalTheory.SecLifts.exists_compatible_sections_local | exact GlobalTheory.SecLifts.exists_compatible_sections_local | (intros; apply GlobalTheory.SecLifts.exists_compatible_sections_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescendedTorsionIsometryThetaCoordinates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section

namespace GlobalTheory.DescendIso

theorem isCoordPt_cart (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {f : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (hp : IsGrpPullback P.A P₀.A (spMap f) φ)
    (hw : LBIso P.L (P₀.L.pull φ)) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1)
    {z : baseOver (Sp R) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(Sp K, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => (spMap f).appTop.hom (v₀ i)) := by
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap f ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap f := by
    show (spMap f ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (baseOver (Sp R)).left ⟶ (baseAt t).left := 𝟙 (Sp R)
  have : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp R)))
  exact FullExtend.isCoordPt_move (T := baseOver (Sp R)) (T₀ := baseOver (Sp K)) (spMap f) hp hw σ
    (homAt t ≫ overResι ⊤) ((Category.id_comp _).trans ht) ((Category.comp_id _).trans (Category.id_comp _).symm)
    (FullExtend.isGenSec_base hS P₀ t) hx hk hz H

theorem exists_unit_smul {K C : Type} [Field K] [Field C] (f : K →+* C) {I : Type} (v₀ v : I → K) (c : Cˣ)
    (h : ∀ x, f (v x) = c * f (v₀ x)) : ∃ d : Kˣ, v = (d : K) • v₀ := by
  by_cases h₀ : ∀ x, v₀ x = 0
  · refine ⟨1, funext fun x => f.injective ?_⟩
    simp [h x, h₀ x]
  · push Not at h₀
    obtain ⟨y, hy⟩ := h₀
    have hy' : f (v₀ y) ≠ 0 := (map_ne_zero f).2 hy
    have e : f (v y / v₀ y) = c := by rw [map_div₀, h y, mul_div_assoc, div_self hy', _root_.mul_one]
    have hd : v y / v₀ y ≠ 0 := fun q => c.ne_zero (by rw [← e, q, map_zero])
    refine ⟨Units.mk0 _ hd, funext fun x => f.injective ?_⟩
    rw [h x, Pi.smul_apply, smul_eq_mul, map_mul, Units.val_mk0, e]

theorem isCoordPt_descend (hL : Laws) {K C : Type} [Field K] [IsAlgClosed K] [Field C] [IsAlgClosed C] {f : K →+* C}
    {P₀ : PolAV (Sp K)} {P : PolAV (Sp C)} {φ : P.A.left ⟶ P₀.A.left} (hp : IsGrpPullback P.A P₀.A (spMap f) φ)
    (hw : LBIso P.L (P₀.L.pull φ)) {m : ℕ} (hm : Odd m) (hK : (m : K) ≠ 0) {I : Type}
    {x : I → (baseOver (Sp C) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (m ^ 2) = 1)
    (hk₀ : ∀ i, x₀ i ^ (m ^ 2) = 1)
    {z : baseOver (Sp C) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    (v : I → K) (v' : I → C) (s : Cˣ) (hv : ∀ i, f (v i) = s * v' i)
    (H : IsCoordPt P m x z fun i => fnOf (v' i)) : IsCoordPt P₀ m x₀ z₀ fun i => fnOf (v i) := by
  have hC : (m : C) ≠ 0 := by rw [← map_natCast f]; exact (map_ne_zero f).2 hK
  obtain ⟨a₁, a₂, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K (Sp K) P₀ (𝟙 _) m hm hK I x₀ hk₀
  obtain ⟨-, b₂, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C (Sp C) P (𝟙 _) m hm hC I x hk
  obtain ⟨v₀, h₀⟩ := a₁ z₀
  have q := isCoordPt_cart hL.secBaseChange hp hw hx hk hz h₀
  simp only [← FullExtend.fnOf_map] at q
  obtain ⟨c, hc⟩ := (b₂ z (fun i => f (v₀ i)) v' q).1 H
  refine (a₂ z₀ v₀ v h₀).2 (exists_unit_smul f v₀ v (s * c) fun i => ?_)
  rw [hv, hc, Pi.smul_apply, smul_eq_mul, Units.val_mul, _root_.mul_assoc]

theorem exists_descend : Laws → AllD fun {E} _ _ _ {H} D => ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (o : Full D K) (o' : Full D C), FullExt f o o' → ∀ (I' : FullI o') (ζ : ℕ → Kˣ), (∀ n, 0 < n → (I'.ζ n : C) = f (ζ n)) → ∃ I : FullI o, (∀ n, 0 < n → I.ζ n = ζ n) ∧ ∀ m, Odd m → (∀ (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Theta m v' → (withI o I).Theta m v) ∧ ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := by
  intro hL E _ _ _ H D K C _ _ f o o' hext I' ζ hζ
  obtain ⟨-, hz, φ, hp, hw, -, hev⟩ := hext
  haveI := o.closed
  haveI := o'.closed
  haveI := o.charZero
  haveI := o'.charZero
  obtain ⟨g, hg⟩ := tateIso_differ_by_similitude E H D C _ _ _
    (fun n x y c c' _ _ _ => weilIs_unique_fieldPoint _ _ _ o'.P.isLB C (𝟙 _) n x y c c') o'.I I'
  obtain ⟨ν, h₀, h₁, h₂⟩ := ReZeta.exists_exponent o'.I.ζ I'.ζ o'.I.ζ_prim o'.I.ζ_pow I'.ζ_prim I'.ζ_pow
  have hd : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ g.ν n - ν n := fun n hn => by
    rw [← (o'.I.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, ← (hg n hn).2, h₀ n hn, mul_inv_cancel]
  have hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ) :=
    fun n m hn hm => by
      obtain ⟨a, ha⟩ := hd n hn
      obtain ⟨b, hb⟩ := hd (n * m) (Nat.mul_pos hn hm)
      obtain ⟨c, hc⟩ := h₂ n m hn hm
      obtain ⟨u, w, huw⟩ := h₁ n hn
      push_cast at hb
      exact ⟨⟨m * b + c - a, by linear_combination hb + hc - ha⟩, u, w - u * a, by linear_combination huw + u * ha⟩
  let I : FullI o := LevelTwist.twist o.I g hν
  have hI : ∀ n, 0 < n → ∀ a, spMap f ≫ (I.ev n a).left = (I'.ev n a).left ≫ φ := fun n hn a => by
    rw [(hg n hn).1 a]
    exact (hev n _ hn).symm
  have key : ∀ m, Odd m → ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) →
      (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := fun m hm j hj z v v' s hv Q =>
    isCoordPt_descend hL hp hw hm (Nat.cast_ne_zero.2 hm.pos.ne') (hI _ (pow_pos hm.pos 2))
      (tateIso_ev_pow I' (pow_pos hm.pos 2)) (tateIso_ev_pow I (pow_pos hm.pos 2)) (hI j hj z) v v' s hv Q
  refine ⟨I, fun n hn => Units.ext (f.injective ?_), fun m hm => ⟨fun v v' s hv Q => ?_, key m hm⟩⟩
  · rw [← hζ n hn, (hg n hn).2, Units.val_zpow_eq_zpow_val, hz n hn, ← map_zpow₀, ← Units.val_zpow_eq_zpow_val]
    rfl
  · have e : I.ev 1 0 = 1 := (I.ker 1 one_pos 0).2 ⟨0, by simp⟩
    have e' : I'.ev 1 0 = 1 := (I'.ker 1 one_pos 0).2 ⟨0, by simp⟩
    have k := key m hm 1 one_pos 0 v v' s hv
    rw [e, e'] at k
    obtain ⟨-, -, a₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K (Sp K) o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
      (I.ev (m ^ 2)) (tateIso_ev_pow I (pow_pos hm.pos 2))
    obtain ⟨-, -, b₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C (Sp C) o'.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
      (I'.ev (m ^ 2)) (tateIso_ev_pow I' (pow_pos hm.pos 2))
    exact (a₃ v).2 (k ((b₃ v').1 Q))

end GlobalTheory.DescendIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormCorrectionOfVanishingAfterBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_correction_of_vanishing_after_baseChange : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (H₀ : LB X₀) (w₀ : LB.Iso H₀ (H.pull π)) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → w₀.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (π) z ∈ (H).U k → z ∈ (H₀).U k' → gs (π) z _ ((s j).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → ∀ t : ℕ, FirstCohomologyVanishes (pw H₀ t) → (∀ σ : LB.Sec (pw H₀ t), ∃ P : MvPolynomial (Fin (n + 1)) K, P.IsHomogeneous t ∧ ∀ k : H₀.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f₀) ((H₀).U k)) (fun j => (s₀ j).f k) (P)) → ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (H' : LB X') (w : LB.Iso H' (H.pull β)) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (β) z ∈ (H).U k → z ∈ (H').U k' → gs (β) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ F : MvPolynomial (Fin (n + 1)) A, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (β ≫ f) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous t ∧ (∀ d, g (MvPolynomial.coeff d G) = 0) ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F - G) = 0) := by
  first | exact @GlobalTheory.FormCorr.exists_form_correction | exact GlobalTheory.FormCorr.exists_form_correction | (intros; apply GlobalTheory.FormCorr.exists_form_correction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullObjectOfThetaPointInAlgClosedSubfield
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ThetaDescent

theorem exists_full_of_theta_in_subfield : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K κ : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field κ] [IsAlgClosed κ] (i : K →+* κ) (m : ℕ) (ρ z : K) (v : D.La → K) (o' : Full D κ), Odd m → Compat H (m ^ 2) z ρ → o'.ρ = i ρ → (o'.I.ζ (m ^ 2) : κ) = i z → o'.Theta m (fun x => i (v x)) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ (m ^ 2) : K) = z ∧ o.Theta m v := by
  intro hv h6 hU hX hT hE hA E _ _ _ H D l Xo c W₀ Y K κ _ _ _ _ _ i m ρ z v o' hm _ hρ hz hth
  haveI := c.fin
  have hr : H.rt0 ∈ c.F := c.le (baseKA l).ρ.2
  have hζ : zeta l.A ∈ c.F := c.le (baseKA l).ζ.2
  obtain ⟨b, hb⟩ := exists_embedding H c.F hr ρ (i.injective (by rw [map_pow, ← hρ, o'.ρ_sq, map_neg, map_natCast]))
  have hp : IsPrimitiveRoot (i (b ⟨_, hζ⟩)) l.A :=
    ((IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (ζ := ⟨_, hζ⟩)
      (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne') Subtype.val_injective).map_of_injective
        b.injective).map_of_injective i.injective
  obtain ⟨I, hI⟩ := GlobalTheory.TateRoot.exists_tateIso_zeta_eq E H D l κ _ _ _ o'.I l.A _ l.A_pos hp
  obtain ⟨y, ⟨hy, φ, h₁, h₂, h₃, -⟩, -⟩ := (GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hv h6 hU hX hT hE hA E H D l Xo c W₀ Y κ (i.comp b)).1
    { o' with I := I } (fun r h => by
      obtain rfl : r = ⟨_, hr⟩ := Subtype.ext h
      exact hρ.trans (congrArg i hb.symm)) (fun r h => by
      obtain rfl : r = ⟨_, hζ⟩ := Subtype.ext h
      exact hI)
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨o, h₄, h₅⟩ := exists_full hv.1.1 hv.1.2.1.secBaseChangeAny (pullback.snd _ _)
    (IntermediateField.inclusion c.le).toRingHom pullback.condition Y.oF b i y hy o' φ h₁ h₂ h₃ m hm z v hz hth
  exact ⟨o, h₄.trans hb, h₅⟩

end GlobalTheory.Ex.ThetaDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsKernelPolarisationTrivialSpreadLocalisatioStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernelPolarisation_trivial_spread_localisation : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → GlobalTheory.AbLaw.IsProjBy G.hom → KTriv A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → KTriv G' L' := by
  first | exact @GlobalTheory.GenSpread.exists_kTriv | exact GlobalTheory.GenSpread.exists_kTriv | (intros; apply GlobalTheory.GenSpread.exists_kTriv <;> assumption)
end

