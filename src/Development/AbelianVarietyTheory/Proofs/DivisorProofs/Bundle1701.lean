import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneStabilizerAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumTrivSqZeroExtEq
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS.FunDer

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.TangentOrigin GlobalTheory.Frames GlobalTheory.FlagTan
open TrivSqZeroExt hiding map lift
open scoped Classical

theorem primeSpectrum_trivSqZeroExt_eq {L ι : Type} [Field L] (x y : PrimeSpectrum (TrivSqZeroExt L (ι → L))) :
    x = y := by
  have h : ∀ z : PrimeSpectrum (TrivSqZeroExt L (ι → L)), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem primeSpectrum_field_eq {L : Type} [Field L] (x y : PrimeSpectrum L) : x = y :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)

theorem le_preimage_of_unique {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R']
    (hR : ∀ x y : PrimeSpectrum R, x = y) {T : Scheme.{0}} (φ : R →+* R') (x : Sp R ⟶ T) (V : T.Opens)
    (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint R') = s := hR _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint R') ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem top_le_comp {S T U : Scheme.{0}} (f : S ⟶ T) (x : T ⟶ U) (V : U.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ (f ≫ x) ⁻¹ᵁ V := fun s _ => h (Set.mem_univ (f s))

theorem top_le_of_red {L R : Type} [Field L] [CommRing R] (hR : ∀ x y : PrimeSpectrum R, x = y) (ρ : R →+* L)
    {T : Scheme.{0}} {p : Sp R ⟶ T} {z : Sp L ⟶ T} (e : spMap ρ ≫ p = z) {O : T.Opens} (h : ⊤ ≤ z ⁻¹ᵁ O) :
    ⊤ ≤ p ⁻¹ᵁ O :=
  le_preimage_of_unique hR ρ p O (e ▸ h)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem lift_eq {S : Scheme.{0}} {a b : S ⟶ M.X} (h : a ≫ toFlag M = b ≫ toFlag M) (ha : ⊤ ≤ a ⁻¹ᵁ M.off) :
    a = b := by
  have hU : ⊤ ≤ (a ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ha (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have e : a ≫ M.σ = b ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, Category.assoc]
    exact h
  exact (M.existsUnique_lift (a ≫ M.σ) hU).unique rfl e.symm

theorem exists_lift_of_unique {L R : Type} [Field L] [Algebra c.F L] [CommRing R] [Algebra c.F R]
    (hR : ∀ x y : PrimeSpectrum R, x = y) (ρ : R →ₐ[c.F] L) {Q : FrPt Xo c L} {W : FrPt Xo c R} (hd : FrMap ρ W Q)
    {z : Sp L ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ ZW : Sp R ⟶ M.X, ZW ≫ toFlag M = X.ptY W ∧ spMap ρ.toRingHom ≫ ZW = z := by
  have e := (X.ptY_frMap hd).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY W ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_unique hR ρ.toRingHom _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY W) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY W := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap ρ.toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_unique hR ρ.toRingHom _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap ρ.toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, hred⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

theorem red_eq {L : Type} [Field L] [Algebra c.F L] {Q : FrPt Xo c L} {z : Sp L ⟶ M.X}
    (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {R : Type} [CommRing R] [Algebra c.F R]
    {ρ : R →ₐ[c.F] L} {u : FrPt Xo c R} (hu : FrMap ρ u Q) {p : Sp R ⟶ M.X} (hp : p ≫ toFlag M = X.ptY u) :
    spMap ρ.toRingHom ≫ p = z :=
  (lift_eq M (by rw [Category.assoc, hp, X.ptY_frMap hu, hz]) ho).symm

variable {K : Type} [Field K] [Algebra c.F K]

theorem der_dir {ι : Type} [Fintype ι] {Q : FrPt Xo c K} {z : Sp K ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q)
    (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {W : FrPt Xo c (TrivSqZeroExt K (ι → K))} (hW : FrMap (fstHom c.F K (ι → K)) W Q) :
    ∃ ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, ∀ (m : ι → K) (u : FrPt Xo c (DualNumber K))
      (p : Sp (DualNumber K) ⟶ M.X), FrMap (dir c m) W u → p ≫ toFlag M = X.ptY u →
      ∀ (O : M.X.Opens) (g : Γ(M.X, O)) (hp : ⊤ ≤ p ⁻¹ᵁ O), ∃ hZ : ⊤ ≤ ZW ⁻¹ᵁ O,
        (evalPt p O hp g).snd = ∑ k, (evalPt ZW O hZ g).snd k * m k := by
  obtain ⟨ZW, h1, h2⟩ := exists_lift_of_unique M primeSpectrum_trivSqZeroExt_eq _ hW hz ho
  have hZo : ⊤ ≤ ZW ⁻¹ᵁ M.off := top_le_of_red primeSpectrum_trivSqZeroExt_eq _ h2 ho
  refine ⟨ZW, fun m u p hu hp O g hpO => ?_⟩
  have e : p = spMap (dir c m).toRingHom ≫ ZW :=
    (lift_eq M (by rw [Category.assoc, h1, X.ptY_frMap hu, hp]) (top_le_comp _ _ _ hZo)).symm
  subst e
  have hZ : ⊤ ≤ ZW ⁻¹ᵁ O := le_preimage_of_unique primeSpectrum_trivSqZeroExt_eq _ ZW O hpO
  refine ⟨hZ, ?_⟩
  rw [evalPt_spMap_comp _ ZW O hZ hpO]
  exact snd_dir m _

theorem der_vert_eq_zero {y : FrPt Xo c K} {z : Sp K ⟶ M.X} (hz : z ≫ toFlag M = X.ptY y) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {N : FIx Dw → K} {u : FrPt Xo c (DualNumber K)} (h : IsVert y N u)
    (hN : ∀ σ i j, i < j → N (some ⟨σ, i, j⟩) = 0) {p : Sp (DualNumber K) ⟶ M.X} (hp : p ≫ toFlag M = X.ptY u)
    (O : M.X.Opens) (g : Γ(M.X, O)) (h1 : ⊤ ≤ p ⁻¹ᵁ O) : (evalPt p O h1 g).snd = 0 := by
  obtain ⟨y₀, h₀, hs⟩ := h
  have hb : FrBor (fun k => oneAddEps (Multiplicative.ofAdd (diagOf N k))) y₀ u :=
    (frBor_iff_frChg _ _ _).2 ⟨unip K N, fun σ i j hij => by simp [unip, hN σ i j hij, hij.ne],
      fun _ _ => by simp [unip, oneAddEps, diagOf], hs⟩
  have e : p = spMap (cst c K).toRingHom ≫ z := by
    refine (lift_eq M ?_ (top_le_comp _ _ _ ho)).symm
    rw [Category.assoc, hz, X.ptY_frMap h₀, X.ptY_frBor hb, hp]
  subst e
  have hzO : ⊤ ≤ z ⁻¹ᵁ O := le_preimage_of_unique primeSpectrum_field_eq _ z O h1
  rw [evalPt_spMap_comp _ z O hzO h1]
  rfl

theorem der_shift {y : FrPt Xo c K} {z : Sp K ⟶ M.X} (hz : z ≫ toFlag M = X.ptY y) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {N : FIx Dw → K} {v v' : FrPt Xo c (DualNumber K)} (h : IsDef y v) (h' : IsShift N v v')
    {zz : FIx Dw → FrPt Xo c (DualNumber K)} (hzz : ∀ k, IsVert y (Pi.single k (1 : K)) (zz k))
    {p p' : Sp (DualNumber K) ⟶ M.X} {q : FIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hp : p ≫ toFlag M = X.ptY v)
    (hp' : p' ≫ toFlag M = X.ptY v') (hq : ∀ k, q k ≫ toFlag M = X.ptY (zz k)) (O : M.X.Opens) (g : Γ(M.X, O))
    (h1 : ⊤ ≤ p ⁻¹ᵁ O) (h2 : ⊤ ≤ p' ⁻¹ᵁ O) (h3 : ∀ k, ⊤ ≤ q k ⁻¹ᵁ O) :
    (evalPt p' O h2 g).snd = (evalPt p O h1 g).snd + ∑ k, N k * (evalPt (q k) O (h3 k) g).snd := by
  let emb : DualNumber K →ₐ[c.F] TrivSqZeroExt K (Option (FIx Dw) → K) :=
    (TrivSqZeroExt.map (LinearMap.single K (fun _ : Option (FIx Dw) => K) none)).restrictScalars c.F
  have e1 : ∀ a, (emb a).fst = a.fst := fun a => fst_map _ a
  have e2 : ∀ a, (emb a).snd = Pi.single none a.snd := fun a => snd_map _ a
  obtain ⟨W₀, hW₀⟩ := exists_frMap emb v
  let n : FIx Dw → Option (FIx Dw) → K := fun k => Pi.single (some k) 1
  obtain ⟨W, hW, -⟩ := existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)
  have key : ∀ (m : Option (FIx Dw) → K) (z₀ z : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      IsShift (fun k => m (some k)) z₀ z → FrMap (dir c m) W z := fun m z₀ z k₀ k => by
    refine (frMap_iff_frChg hW k₀).2 ?_
    unfold IsShift at k
    convert k using 2 with τ
    · ext i j <;> simp [unip, n, Pi.single_apply]
    · ext <;> simp [unip₀, n, Pi.single_apply]
  have k1 : ∀ m : Option (FIx Dw) → K, m none = 1 → FrMap (dir c m) W₀ v := fun m hm =>
    frMap_of_comp hW₀ (frMap_id v) fun a => by ext <;> simp [e1, e2, Pi.single_apply, hm]
  have kv : FrMap (dir c (Pi.single none 1)) W v :=
    key _ v v (k1 _ (by simp)) (by convert isShift_zero v using 2; simp)
  have hWy : FrMap (fstHom c.F K (Option (FIx Dw) → K)) W y := frMap_comp kv h fun a => by simp
  obtain ⟨ZW, hZW⟩ := der_dir M hz ho hWy
  obtain ⟨hZ1, a1⟩ := hZW _ _ p' (key (fun k => k.elim 1 N) v v' (k1 _ rfl) h') hp' O g h2
  obtain ⟨hZ2, a2⟩ := hZW _ _ p kv hp O g h1
  rw [a1, a2, Fintype.sum_option]
  congr 1
  · simp [Pi.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨y₀, h₀, hk⟩ := hzz k
  obtain ⟨hZ3, a3⟩ := hZW _ _ (q k) (key (Pi.single (some k) 1) y₀ (zz k)
    (frMap_of_comp hW₀ (frMap_comp (χ := (cst c K).comp (red c K)) h h₀ fun _ => rfl) fun a => by
      ext <;> simp [e1, e2, Pi.single_apply]) (by
      convert hk using 2; simp [Pi.single_apply])) (hq k) O g (h3 k)
  rw [a3]
  simp [Pi.single_apply, mul_comm]

theorem evalPt_eq_of_eq {R : Type} [CommRing R] {T : Scheme.{0}} {a b : Sp R ⟶ T} (e : a = b) (O : T.Opens)
    (ha : ⊤ ≤ a ⁻¹ᵁ O) (hb : ⊤ ≤ b ⁻¹ᵁ O) (g : Γ(T, O)) : evalPt a O ha g = evalPt b O hb g := by
  subst e
  rfl

end GlobalTheory.CompHS.FunDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveMapUniversalLineStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_map_universal_line : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (φ : T ⟶ PSpace k N) (L : T.Modules), IsVB L 1 → ∃ (Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB Q 1 ∧ JointEpi s ∧ Rel φ s := by
  first | exact @GlobalTheory.LineQuot.exists_taut_quot | exact GlobalTheory.LineQuot.exists_taut_quot | (intros; apply GlobalTheory.LineQuot.exists_taut_quot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationPullbackStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_relation_pullback : ∀ (k : Type) [CommRing k] (N : ℕ) (S T : Scheme.{0}) (g : S ⟶ T) (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Rel φ s → Rel (g ≫ φ) fun j => (Scheme.Modules.pullback g).map (s j) := by
  first | exact @GlobalTheory.LineQuot.rel_pullback | exact GlobalTheory.LineQuot.rel_pullback | (intros; apply GlobalTheory.LineQuot.rel_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationUniqueQuotientStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_relation_unique_quotient : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q Q' : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)) (s' : Fin (N + 1) → (L ⟶ Q')) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s → Rel φ s → Rel φ s' → ∃ e : Q ⟶ Q', ∀ j, s j ≫ e = s' j := by
  first | exact @GlobalTheory.LineQuot.exists_factor_of_rel | exact GlobalTheory.LineQuot.exists_factor_of_rel | (intros; apply GlobalTheory.LineQuot.exists_factor_of_rel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatDarbouxCoordsRationalMatrixIffRatPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratDarbouxCoords_rationalMatrix_iff_ratPair : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
  first | exact @GlobalTheory.RatDarbouxPointsD.ratL_iff_ratPair | exact GlobalTheory.RatDarbouxPointsD.ratL_iff_ratPair | (intros; apply GlobalTheory.RatDarbouxPointsD.ratL_iff_ratPair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePosPowAffineBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_pos_pow_affine_base : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), L.IsLB → RelAmple B L → ∀ a : ℕ, 1 ≤ a → RelAmple B (GlobalTheory.AbLaw.pw L (a : ℤ)) := by
  first | exact @GlobalTheory.PowAmple.relAmple_pw | exact GlobalTheory.PowAmple.relAmple_pw | (intros; apply GlobalTheory.PowAmple.relAmple_pw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiPolarizationFiniteExtension
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusPart

theorem exists_finite_polDescent : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (c : O →+* O) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (j₀ : OAct O B) (P : Out.PolAV (Sp Ω))
    (j : OAct O P.A) (ψ : P.A.left ⟶ B.left), IsActPull j j₀ (spMap (algebraMap K Ω)) ψ → IsRosati c P j →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧ ∃ (P₁ : Out.PolAV (Sp F)) (j₁ : OAct O P₁.A)
      (ψ₁ : P₁.A.left ⟶ B.left), IsActPull j₁ j₀ (spMap (algebraMap K F)) ψ₁ ∧ IsRosati c P₁ j₁ := by
  intro O _ _ c K Ω _ _ _ _ B _ hB j₀ P j ψ hpull hros
  haveI := hB.comm
  haveI := hB.proper
  haveI := P.isAb.comm
  obtain ⟨F, hF, H⟩ := GlobalTheory.LBDescent.exists_finite_subextension_cls K Ω B.left P.A.left B.hom P.A.hom ψ
    hpull.1.1 P.L P.isLB
  let f : Sp F ⟶ Sp K := spMap (algebraMap K F)
  let A₁ := (Over.pullback f).obj B
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj f B hB
  haveI := hA₁.comm
  haveI := hA₁.smooth
  haveI := hA₁.proper
  have hψ₁ : IsActPull (OAct.pullback f B j₀) j₀ f (pullback.fst B.hom f) := exists_isActPull f j₀
  have hcomp : spMap (algebraMap F Ω) ≫ f = spMap (algebraMap K Ω) := by
    simp only [f, spMap]
    rw [← Spec.map_comp]
    congr 1
  have w : ψ ≫ B.hom = (P.A.hom ≫ spMap (algebraMap F Ω)) ≫ f := by
    rw [Category.assoc, hcomp]
    exact hpull.1.1.w
  let jm : P.A.left ⟶ A₁.left := pullback.lift ψ (P.A.hom ≫ spMap (algebraMap F Ω)) w
  have hjf : jm ≫ pullback.fst B.hom f = ψ := pullback.lift_fst _ _ _
  have hjs : jm ≫ A₁.hom = P.A.hom ≫ spMap (algebraMap F Ω) := pullback.lift_snd _ _ _
  have hj : IsGrpPullback P.A A₁ (spMap (algebraMap F Ω)) jm :=
    IsGrpPullback.cancel hψ₁.1 (hpull.1.congr hcomp.symm hjf.symm) hjs
  obtain ⟨x, hx⟩ := H A₁.left A₁.hom (pullback.fst B.hom f) (IsPullback.of_hasPullback _ _) jm hjf hjs
  obtain ⟨L₁, hL₁, rfl⟩ := CechPic.cls_surj x
  have hw : LBIso P.L (L₁.pull jm) := by
    rw [← CechPic.cls_eq_iff P.isLB (pull_isLB hL₁ jm), CechPic.cls_pull hL₁ jm (pull_isLB hL₁ jm)]
    exact hx.symm
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim F A₁ hA₁
  have hd := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend F Ω (algebraMap F Ω) A₁ P.A jm L₁ P.L hA₁ hj hL₁ P.isLB hw
  have ha := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension F Ω (algebraMap F Ω) A₁ P.A jm hj L₁ P.L hL₁
    P.isLB hw P.isAb.proper P.ample P.ktriv
  let P₁ : Out.PolAV (Sp F) :=
    { A := A₁, isAb := hA₁, g := g, smoothDim := hg, L := L₁, isLB := hL₁, rigid := hd.1 P.rigid,
      sym := hd.2.1 P.sym, ample := ha.2.1, ktriv := ha.2.2 }
  have comm : ∀ b, (j.act b).left ≫ jm = jm ≫ ((OAct.pullback f B j₀).act b).left := fun b => by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hjf, hψ₁.2 b, ← Category.assoc, hjf, hpull.2 b]
    · show (j.act b).left ≫ jm ≫ A₁.hom = jm ≫ ((OAct.pullback f B j₀).act b).left ≫ A₁.hom
      rw [Over.w ((OAct.pullback f B j₀).act b), hjs, ← Category.assoc, Over.w (j.act b)]
  exact ⟨F, hF, P₁, OAct.pullback f B j₀, pullback.fst B.hom f, hψ₁, fun a =>
    GlobalTheory.RosatiDescent.rosatiAdj_descend (algebraMap F Ω) hA₁ hj hL₁ P.isLB hw (comm a) (comm (c a)) (hros a)⟩

end GlobalTheory.TorusPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiNegative_descends_fieldExtension_curve : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (k' : Type) [Field k'] [Algebra k k'], ∃ (C' : Scheme.{0}) (_ : Algebra k' Γ(C', ⊤)) (π : C' ⟶ C), IsCurve k' C' ∧
      ∀ F : C.Modules, SemiNeg k' ((Scheme.Modules.pullback π).obj F) → SemiNeg k F := by
  first | exact @GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange | exact GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange | (intros; apply GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralTsumUnfoldOfCosetRepresentatives
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal Pointwise

namespace GlobalTheory.ResLine

theorem setLIntegral_tsum_unfold (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) (Γ Λ : Subgroup G) [Countable Γ] (T : Set Γ) (𝓕 D : Set G)
    (hμ : μ.IsHaarMeasure) (hle : Λ ≤ Γ)
    (hT : ∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ)
    (hF : IsFundamentalDomain Γ 𝓕 μ) (hD : IsFundamentalDomain Λ D μ)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Λ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, ∑' t : T, f (t.1.1 * g) ∂μ = ∫⁻ g in D, f g ∂μ := by
  haveI : Countable Λ := (Subgroup.inclusion_injective hle).countable
  let e0 : T × Λ → Γ := fun p => Subgroup.inclusion hle p.2 * p.1.1
  have hbij : Function.Bijective e0 := by
    constructor
    · rintro ⟨⟨t, ht⟩, l⟩ ⟨⟨s, hs⟩, m⟩ h
      simp only [e0] at h
      have hts : t = s := by
        refine (hT (Subgroup.inclusion hle l * t)).unique ⟨ht, ?_⟩ ⟨hs, ?_⟩
        · simp
        · rw [h]; simp
      subst hts
      have := Subgroup.inclusion_injective hle (mul_right_cancel h)
      subst this
      rfl
    · intro γ
      obtain ⟨t, ⟨ht, hm⟩, -⟩ := hT γ
      refine ⟨(⟨t, ht⟩, ⟨_, hm⟩), ?_⟩
      apply Subtype.ext
      simp [e0]
  have h1 : ∀ t : T, ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ
      = ∑' l : Λ, ∫⁻ g in D ∩ (e0 (t, l)) • 𝓕, f g ∂μ := by
    intro t
    have h2 : ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ = ∫⁻ g in t.1 • 𝓕, f g ∂μ :=
      (measurePreserving_smul t.1 μ).setLIntegral_comp_emb (measurableEmbedding_const_smul t.1) f 𝓕
    rw [h2, hD.setLIntegral_eq_tsum' f]
    refine tsum_congr fun l => ?_
    have h3 : l • t.1 • 𝓕 = (e0 (t, l)) • 𝓕 := by
      simp only [e0, mul_smul]
      rfl
    rw [h3, Set.inter_comm]
    refine lintegral_congr fun x => ?_
    exact hinv _ (l⁻¹).2 x
  rw [lintegral_tsum (f := fun (t : T) g => f (t.1.1 * g)) (fun t : T => (hf.comp (measurable_const_mul t.1.1)).aemeasurable),
    hF.setLIntegral_eq_tsum f D, ← (Equiv.ofBijective e0 hbij).tsum_eq, ENNReal.tsum_prod']
  exact tsum_congr h1

end GlobalTheory.ResLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneStabilizerActionStatement
section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_plane_stabilizer_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ (r : ℕ) (X' Y' : Matrix (Fin n) (Fin (r + 1)) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) →
      ∃ (P : Subgroup (GAd σ (c₀ • W.J.map σ))) (π : P →* GAd σ (c₀ • W₁.J.map σ)) (T : P →* (AE F E)ˣ),
        (∀ p, p ∈ P ↔ ∃ t : AF F ⊗[F] E, (matHom _ σ _ p).1 *ᵥ (fun i => inclR (F := F) (AF F) (H.x i)) = t • fun i => inclR (F := F) (AF F) (H.x i)) ∧
        (∀ p : P, ∃ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∃ m, IsLevi (W₁ := W₁) H (T p) 1 m ∧
          (p : GAd σ (c₀ • W.J.map σ)) = u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M (π p)) ∧
        (∀ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∀ t m y, IsLevi (W₁ := W₁) H t 1 m →
          u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y ∈ P) ∧
        Continuous π ∧ Continuous T ∧
        ∃ A : Matrix (Fin n₁) (Fin n) E, A * H.ι = 1 ∧ ∀ p : P, (matHom _ σ _ (π p)).1 =
          GlobalTheory.SiegelSet.adMat F A * (matHom _ σ _ (p : GAd σ (c₀ • W.J.map σ))).1 * GlobalTheory.SiegelSet.adMat F H.ι := by
  first | exact @GlobalTheory.StabLine.exists_stab_decomp | exact GlobalTheory.StabLine.exists_stab_decomp | (intros; apply GlobalTheory.StabLine.exists_stab_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceMultiplicationDerivativeWordIteratedFDerivStatement
section
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_multiplicationDerivativeWord_iteratedFDeriv : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (u : κ → mixedEmbedding.mixedSpace F) (i : ℕ) (vs : List (κ → mixedEmbedding.mixedSpace F))
        (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
            vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x := by
  first | exact @GlobalTheory.WeilL2Words.slice_word_mul_fderivs | exact GlobalTheory.WeilL2Words.slice_word_mul_fderivs | (intros; apply GlobalTheory.WeilL2Words.slice_word_mul_fderivs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureBis
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_fibre_not_in_closure : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → SpecialFibreNotInClosure p O := by
  first | exact @GlobalTheory.WeilIntegral.specialFibreNotInClosure | exact GlobalTheory.WeilIntegral.specialFibreNotInClosure | (intros; apply GlobalTheory.WeilIntegral.specialFibreNotInClosure <;> assumption)
end

