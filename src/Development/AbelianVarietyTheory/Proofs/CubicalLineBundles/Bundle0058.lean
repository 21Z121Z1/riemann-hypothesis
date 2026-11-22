import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCMPairingFamilyOfPolarisationDiagonalComplex
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0036
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0052
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConjStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (a : OAct (OK H) P.A), Function.Injective σ → P.g = 1 → ∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) := by
  first | exact @GlobalTheory.CurveAdjoint.lamEq_act_bar | exact GlobalTheory.CurveAdjoint.lamEq_act_bar | (intros; apply GlobalTheory.CurveAdjoint.lamEq_act_bar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.PairingScheme

theorem exists_unitOn {K : Type} [CommRing K] (c : Γ(Sp K, ⊤)ˣ) : ∃ z : Kˣ, unitOn z = c := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c, ?_⟩
  ext
  simp [unitOn]

theorem comp_pow_eq_one {S : Scheme.{0}} {T X A : Over S} [GrpObj X] [GrpObj A] (f : X ⟶ A) [IsMonHom f]
    {x : T ⟶ X} {k : ℕ} (hx : x ^ k = 1) : (x ≫ f) ^ k = 1 := by
  rw [← MonObj.pow_comp, hx, MonObj.one_comp]

theorem pull_pow_eq_one {S : Scheme.{0}} {T T' X : Over S} [GrpObj X] (t : T' ⟶ T)
    {x : T ⟶ X} {k : ℕ} (hx : x ^ k = 1) : (t ≫ x) ^ k = 1 := by
  rw [← MonObj.comp_pow, hx, MonObj.comp_one]

theorem weilIs_iff_of_lamEq : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → ∀ (T : Over (Sp R)) (k : ℕ) (x : T ⟶ X.A) (y : T ⟶ Y.A) (c : Γ(T.left, ⊤)ˣ), 0 < k → x ^ k = 1 → y ^ k = 1 → (Out.WeilIs A.A A.L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs B.A B.L k (x ≫ g₁) (y ≫ g₂) c) := by
  intro hL R _ _ _ X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ hlam T k x y c hk hx hy
  have hN : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  obtain ⟨T₀, x₀, y₀, hx₀, hy₀, huniv, hsep⟩ := GlobalTheory.T.exists_universal_torsion_pair_polAV hL R X Y k hk
  obtain ⟨a, ha, -⟩ := (hL.weil (Sp R) A k T₀).1 _ _ (comp_pow_eq_one f₁ hx₀) (comp_pow_eq_one f₂ hy₀)
  obtain ⟨b, hb, -⟩ := (hL.weil (Sp R) B k T₀).1 _ _ (comp_pow_eq_one g₁ hx₀) (comp_pow_eq_one g₂ hy₀)
  have hab : a = b := by
    apply Units.ext
    refine hsep _ _ fun k' _ _ _ β t => ?_
    have hw := (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL R X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ k' β).1 hlam
    have ha' := CommPairing.weilIs_pull hL.globalFns A.isAb A.isLB t ha
    have hb' := CommPairing.weilIs_pull hL.globalFns B.isAb B.isLB t hb
    obtain ⟨z, hz⟩ := exists_unitOn (K := k') (Units.map t.left.appTop.hom.toMonoidHom a)
    have hx' := pull_pow_eq_one t hx₀
    have hy' := pull_pow_eq_one t hy₀
    rw [← Category.assoc, ← Category.assoc] at ha' hb'
    have h₁ := (hw k (t ≫ x₀) (t ≫ y₀) z hk hx' hy').1 (by rw [hz]; exact ha')
    rw [hz] at h₁
    have h₂ := ((hL.weil (Sp R) B k _).1 _ _ (comp_pow_eq_one g₁ hx') (comp_pow_eq_one g₂ hy')).unique h₁ hb'
    exact congrArg Units.val h₂
  subst hab
  obtain ⟨t, rfl, rfl⟩ := huniv T x y hx hy
  have ha' := CommPairing.weilIs_pull hL.globalFns A.isAb A.isLB t ha
  have hb' := CommPairing.weilIs_pull hL.globalFns B.isAb B.isLB t hb
  rw [← Category.assoc, ← Category.assoc] at ha' hb'
  constructor
  · intro H
    rw [((hL.weil (Sp R) A k _).1 _ _ (comp_pow_eq_one f₁ hx) (comp_pow_eq_one f₂ hy)).unique H ha']
    exact hb'
  · intro H
    rw [((hL.weil (Sp R) B k _).1 _ _ (comp_pow_eq_one g₁ hx) (comp_pow_eq_one g₂ hy)).unique H hb']
    exact ha'

end GlobalTheory.PairingScheme
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_lieLattices_cmTriple_baseChange : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (T : PAT H (Sp (𝓞 K))) (T' : PAT H (Sp (𝓞 K'))) (_ : SABMap T'.t T.t (spMap (RingOfIntegers.mapRingHom j))) (F : GenFib T.pol) (F' : GenFib T'.pol) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K' (Fin F'.P₀.g → K')), F.IsHerm h → F'.IsHerm h' → deg h' F'.lieLat = deg h F.lieLat ∧ ∀ τ : 𝓞 E →+* 𝓞 K, deg h' (F'.eigLat T'.t.act ((RingOfIntegers.mapRingHom j).comp τ)) = deg h (F.eigLat T.t.act τ) := by
  first | exact @GlobalTheory.CM.LieBaseChange.deg_lieLat_eigLat_baseChange | exact GlobalTheory.CM.LieBaseChange.deg_lieLat_eigLat_baseChange | (intros; apply GlobalTheory.CM.LieBaseChange.deg_lieLat_eigLat_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieEigenbasisGenericFibreCmTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_eigenbasis_genericFibre_cmTriple : Out.SecTwistSt → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))) (oa : T.pol.OAct (𝓞 E)) (S : Set (E →+* ℂ)) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), oa.act = T.t.act.act → Function.Bijective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → HasType H T.t.act ρ 1 0 → ∃ (x : KeyIn K) (φ : x.P.A.left ⟶ T.pol.A.left) (τ : Fin x.P.g ≃ S), IsFibreOf T.pol x (gmap K) φ ∧ x.P.g = Module.finrank ℚ E / 2 ∧ IsLieType T.pol oa x φ τ lab := by
  first | exact @GlobalTheory.LamF.exists_eigenbasis_fibre | exact GlobalTheory.LamF.exists_eigenbasis_fibre | (intros; apply GlobalTheory.LamF.exists_eigenbasis_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCMPairingFamilyOfPolarisationDiagonalComplexStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCMPairingFamily_of_polarisationDiagonal_complex : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ω : ℂ) (C : Ell H ℂ ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp ℂ)) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)), IsKForm D ε h → (∀ x ∈ L, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → PureType.IsHomFamily T.t C.P.A C.P.L C.v L (2 * ω - 1) Set.univ ψ → IsFam C T h L ψ := by
  first | exact @GlobalTheory.CM.FamPairing.isFam_of_isHomFamily | exact GlobalTheory.CM.FamPairing.isFam_of_isHomFamily | (intros; apply GlobalTheory.CM.FamPairing.isFam_of_isHomFamily <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamEqOfWeilIsAllPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

private theorem pnsmulPt_eq_pow {S : Scheme.{0}} {G T : Over S} [GrpObj G] (n : ℕ) (a : T ⟶ G) :
    pnsmulPt n a = a ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem lamEq_of_weilIs_all_points : Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A) (g : A.A ⟶ A.A), IsMonHom f → IsMonHom g → (∀ (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x y : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k → pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k y = toUnit Tb ≫ η[A.A] → (Out.WeilIs B.A B.L k (x ≫ f) (y ≫ f) c ↔ Out.WeilIs A.A A.L k (x ≫ g) y c)) → LamEq B.L f f A.L g (𝟙 A.A) := by
  intro laws K _ _ A B f g hf hg H
  have hβ : Function.Injective ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)) :=
    (algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective (𝓞 K) K)
  refine (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring laws (𝓞 K) A A B A f f g (𝟙 A.A) hf hf hg inferInstance (AlgebraicClosure K)
    ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K))).2 inferInstance hβ ?_
  intro n p q c hn hp hq
  rw [Category.comp_id]
  refine H _ n p q (unitOn c) hn ?_ ?_
  · rw [pnsmulPt_eq_pow, hp]; rfl
  · rw [pnsmulPt_eq_pow, hq]; rfl

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormalisedDegreeCmEigenLineEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem splits_of_injective_label {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    {lab : (E →+* ℂ) → (E →+* K)} (hl : Function.Injective lab) : GlobalTheory.CM.Splits E K := by
  rw [GlobalTheory.CM.splits_iff_card]
  refine le_antisymm GlobalTheory.CM.card_ringHom_le_finrank ?_
  have h1 : Nat.card (E →+* ℂ) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card]
    exact NumberField.Embeddings.card E ℂ
  rw [← h1]
  exact Nat.card_le_card_of_injective lab hl

theorem ndeg_vecLine_eq : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), IsFibreOf A x (gmap K) φ → Function.Injective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → IsLieType A oa x φ τ lab → ∀ (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ℓ.ndeg = (logOm E χ).re / 2 := by
  intro hD hU hL E _ _ _ _ H _ χ hχ hstar K _ _ A oa x φ S τ lab ρ hfib hl hρ hS hLie i ℓ hℓ
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (GlobalTheory.LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).1 hfib
  have hoa : ∃ act : OAct (𝓞 E) A.A, act.act = oa.act := by
    exact (GlobalTheory.LamF.ringAct_iff_oAct (𝓞 E) _ A.A).1 oa.1
  obtain ⟨act, hact⟩ := hoa
  have hsplit : GlobalTheory.CM.Splits E K := splits_of_injective_label hl
  have htype : HasType H act ρ 1 0 :=
    GlobalTheory.LamF.LieType.hasType_of_isLieType E H K A x φ hf oa act S τ lab ρ hact hl hS hLie
  have hlam : ∀ a, LamEq A.L (act.act a) (𝟙 A.A) A.L (𝟙 A.A) (act.act (H.bar a)) := by
    intro a
    have hr := oa.rosati a
    rw [← hact, hstar] at hr
    exact (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hL.globalFns _ A (act.act a) (act.act (H.bar a))
      (act.hom a) (act.hom (H.bar a))).1 hr
  set F : GenFib A := GenFib.mk x.P φ hf x.v x.basis with hF
  obtain ⟨⟨h, hh⟩, -⟩ := GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL K A F
  set t : 𝓞 E →+* 𝓞 K := RingOfIntegers.mapRingHom (lab (τ i)) with ht
  have htv : ∀ a : 𝓞 E, (t a : K) = lab (τ i) (a : E) := fun a => rfl
  have hti : t H.rt = ρ := by
    apply RingOfIntegers.ext
    rw [htv]
    exact (hS (τ i)).1 (τ i).2
  have hdeg := GlobalTheory.T.two_mul_deg_eigenLattice_polarizedAbelianScheme hD hU hL E H χ hχ K ρ A act hlam hsplit hρ htype F h hh t hti
  have hline : deg h (F.eigLat act t) = ℓ.ndeg := by
    refine GlobalTheory.LamF.deg_eq_ndeg_of_line K (Fin x.P.g → K) h (F.eigLat act t) (Pi.single i 1) ℓ ?_ hℓ.1 ?_ ?_
    · intro h0
      have := congrFun h0 i
      simp at this
    · intro z
      rw [GlobalTheory.LamF.EigLine.mem_eigLat_iff E K A x φ hf oa act S τ lab hact hl hLie i t htv z]
      constructor
      · rintro ⟨hz, r, rfl⟩
        refine ⟨r, ?_, ?_⟩
        · exact (GlobalTheory.T.mem_lieVector_line_ideal_iff_mem_lie_lattice K A x φ hf i ℓ hℓ r).2 hz
        · ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
      · rintro ⟨c, hc, rfl⟩
        refine ⟨?_, c, ?_⟩
        · have := (GlobalTheory.T.mem_lieVector_line_ideal_iff_mem_lie_lattice K A x φ hf i ℓ hℓ c).1 hc
          convert this using 1
          ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
        · ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
    · exact GlobalTheory.CM.LieMetric.vecLine_norm_sq_eq_form hU hL K A x φ hf h hh i ℓ hℓ
  have hre := congrArg Complex.re hdeg
  rw [Complex.ofReal_re] at hre
  rw [← hline]
  linarith

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekindStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_generic_isogenous_dedekind : Out.Laws → Out.Laws2 → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (B : Over (Sp R)) [GrpObj B] (Ψ : P.A ⟶ B) (M : LB B.left) (B₀ : Over (Sp K)) [GrpObj B₀] (φ : B₀.left ⟶ B.left) (M₀ : LB B₀.left), IsAbelianScheme B → M.IsLB → M₀.IsLB → IsFinite Ψ.left → Flat Ψ.left → Surjective Ψ.left → IsGrpPullback B₀ B (spMap (algebraMap R K)) φ → LBIso M₀ (M.pull φ) → Out.RelAmple B₀ M₀ → Out.RelAmple B M := by
  first | exact @GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous | exact GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous | (intros; apply GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous <;> assumption)
end

