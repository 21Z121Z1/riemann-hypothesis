import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3468
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfSmallTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0090

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupSmulTopEqTopOfForallMaximalOverNat
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory

theorem sup_smul_top_eq_top_of_maximal {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (N : Submodule (𝓞 E) X) (n : ℕ) (hn : 0 < n)
    (h : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → N ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤) :
    N ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) = ⊤ := by
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  suffices key : ∀ I : Ideal (𝓞 E), Ideal.span {(n : 𝓞 E)} ≤ I → N ⊔ I • (⊤ : Submodule (𝓞 E) X) = ⊤ from
    key _ le_rfl
  intro I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro hI
    exfalso
    apply hn0
    have : (n : 𝓞 E) ∈ (0 : Ideal (𝓞 E)) := hI (Ideal.mem_span_singleton_self _)
    simpa using this
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff.mp hx, Submodule.top_smul, sup_top_eq]
  | h₃ a p ha hp ih =>
    intro hI
    have hpI : (p : Ideal (𝓞 E)).IsPrime := Ideal.isPrime_of_prime hp
    have hpmax : p.IsMaximal := hpI.isMaximal hp.ne_zero
    have hnpa : (n : 𝓞 E) ∈ p * a := hI (Ideal.mem_span_singleton_self _)
    have hnp : (n : 𝓞 E) ∈ p := (Ideal.mul_le_left : p * a ≤ p) hnpa
    have h1 := h p hpmax hnp
    have h2 := ih (hI.trans (Ideal.mul_le_right : p * a ≤ a))
    apply top_unique
    calc (⊤ : Submodule (𝓞 E) X) = N ⊔ p • (N ⊔ a • ⊤) := by rw [h2, h1]
      _ = N ⊔ (p • N ⊔ p • a • ⊤) := by rw [Submodule.smul_sup]
      _ ≤ N ⊔ (p * a) • ⊤ := by
        rw [Submodule.mul_smul, ← sup_assoc]
        exact sup_le_sup_right (sup_le le_rfl (Submodule.smul_le_right)) _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBundleLevelOdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_bundle_level_odd : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (β₀ : cycAway M →+* k) (z₀ : kˣ), x₀ ≫ t = spMap β₀ → (z₀ : k) = β₀ (zetaAway M) → (∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x₀) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z₀ ^ (2 * omegaStd a b)))) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S) (β : cycAway M →+* k') (z : k'ˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k') = β (zetaAway M) → ∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b))) := by
  first | (exact @GlobalTheory.WeilOpenLocus.weil_open) | (exact GlobalTheory.WeilOpenLocus.weil_open) | (intros; apply GlobalTheory.WeilOpenLocus.weil_open  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTranslateCoefficientsZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_translate_coefficients_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ t.G.left) (W : t.G.left.Opens), W ≤ t.G.hom ⁻¹ᵁ U.1 → ⊤ ≤ g₀ ⁻¹ᵁ W → ∀ c : Fin n → S, (∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), ∑ a, ρ (c a) * (valR (wt a) O f).snd = 0) → c = 0 := by
  first | exact @GlobalTheory.VertSpan.coeffs_zero | exact GlobalTheory.VertSpan.coeffs_zero | (intros; apply GlobalTheory.VertSpan.coeffs_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoEvEqAtLcmLevelStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIso_ev_eq_at_lcm_level : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop),
  (∀ n, 0 < n → ∀ x y c c', e n x y c → e n x y c' → c = c') → ∀ J J' : TateIso D k Q act e, J.ζ l.M' = J'.ζ l.M' →
  (∀ a, J.ev l.A a = J'.ev l.A a) →
  (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M a = J'.ev l.M a) →
  ∀ a, J.ev l.M' a = J'.ev l.M' a := by
  first | exact @GlobalTheory.LowDat.tateIso_ev_lcm_eq | exact GlobalTheory.LowDat.tateIso_ev_lcm_eq | (intros; apply GlobalTheory.LowDat.tateIso_ev_lcm_eq <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoLatticePartSurjectiveCoisotropicKernel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

open GlobalTheory.Ex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_nsmul_of_dvd (D : Datum H) {n : ℕ} (hn : 0 < n) {b : D.La} (h : ∀ a, (n : ℤ) ∣ D.EF b a) :
    ∃ e, b = n • e := by
  choose f hf using h
  have hn' : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hn.ne'
  let g : D.La →ₗ[ℤ] ℤ :=
    { toFun := f
      map_add' := fun a a' => mul_left_cancel₀ hn' (by rw [mul_add, ← hf, ← hf, ← hf, map_add])
      map_smul' := fun c a => mul_left_cancel₀ hn' (by
        rw [← hf, map_smul, hf, smul_eq_mul, RingHom.id_apply, smul_eq_mul, mul_left_comm]) }
  obtain ⟨e, he⟩ := D.unimod.2 g
  refine ⟨e, D.unimod.1 (LinearMap.ext fun a => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, he, nsmul_eq_mul]
  exact hf a

theorem exists_linear_lift {R M X : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup X] [Module R X] (n : ℕ) (Y : M → X) (hadd : ∀ a b, ∃ e, Y (a + b) = Y a + Y b + n • e)
    (hsmul : ∀ (c : R) a, ∃ e, Y (c • a) = c • Y a + n • e) : ∃ y : M →ₗ[R] X, ∀ a, ∃ e, y a = Y a + n • e := by
  let S : Submodule R X := LinearMap.range (n • LinearMap.id : X →ₗ[R] X)
  have mem : ∀ x : X, x ∈ S ↔ ∃ e, n • e = x := fun x => Iff.rfl
  have h0 : ∀ e : X, S.mkQ (n • e) = 0 := fun e => (Submodule.Quotient.mk_eq_zero S).2 ((mem _).2 ⟨e, rfl⟩)
  let g : M →ₗ[R] X ⧸ S :=
    { toFun := fun a => S.mkQ (Y a)
      map_add' := fun a b => by
        obtain ⟨e, he⟩ := hadd a b
        rw [he, map_add, h0, add_zero, map_add]
      map_smul' := fun c a => by
        obtain ⟨e, he⟩ := hsmul c a
        rw [he, map_add, h0, add_zero, map_smul, RingHom.id_apply] }
  obtain ⟨h, hh⟩ := Module.projective_lifting_property S.mkQ g (Submodule.mkQ_surjective S)
  refine ⟨h, fun a => ?_⟩
  have := congrArg (fun φ : M →ₗ[R] X ⧸ S => φ a) hh
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, g, LinearMap.coe_mk, AddHom.coe_mk] at this
  obtain ⟨e, he⟩ := (mem _).1 ((Submodule.Quotient.eq S).1 this)
  exact ⟨e, by rw [he, add_sub_cancel]⟩

theorem torus_pair (D : Datum H) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)) (hev : D₀.PsiEven)
    (hB : D₀.TauBimult) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F)
    (n : ℕ) (hn : 0 < n) (t t' : Multiplicative D₀.X →* Fˣ) (ht : t ^ n = 1) (ht' : t' ^ n = 1) :
    ∃ b b' : D.La, (∃ e, (I.ev n b).y = n • e) ∧
      (∀ a, I.ζ n ^ D.EF b a = t (Multiplicative.ofAdd (I.ev n a).y)) ∧
      (∀ a, I.ζ n ^ D.EF b' a = t' (Multiplicative.ofAdd (I.ev n a).y)) ∧ ((∃ e, b = b' + n • e) → t = t') := by
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D₀ hev hB F ⊤ fun _ => trivial
  have hGt := GtValues.points_correspond R D₀ hev hB F N ν
  have hWp := WeilValues.weil_eq_values GtValues.points_correspond (brFam hL hL₂) R D₀ hev hB F N ν n hn
  have G := hGt.2.2.2.2 n
  choose Q hQ using fun a => (G.1 (I.ev n a)).exists
  let tr : (Multiplicative D₀.X →* Fˣ) → (Multiplicative N.X →* Fˣ) := fun s =>
    s.comp (AddEquiv.toMultiplicative ν.eX).toMonoidHom
  have trn : ∀ s : Multiplicative D₀.X →* Fˣ, s ^ n = 1 → tr s ^ n = 1 := fun s hs => by
    refine MonoidHom.ext fun χ => ?_
    have := congrArg (fun g : Multiplicative D₀.X →* Fˣ => g ((AddEquiv.toMultiplicative ν.eX).toMonoidHom χ)) hs
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this ⊢
    exact this
  have one : ∀ (s : Multiplicative D₀.X →* Fˣ) (hs : s ^ n = 1), ∃ b, N.QEq (Q b) (N.qTor (tr s) (trn s hs)) ∧
      ∀ a, I.ζ n ^ D.EF b a = s (Multiplicative.ofAdd (I.ev n a).y) := by
    intro s hs
    obtain ⟨p₀, hp₀⟩ := G.2.1 (N.qTor (tr s) (trn s hs))
    obtain ⟨b, hb⟩ := I.onto n hn p₀
    have hq := (G.2.2 _ _ _ _ (hQ b) hp₀).1 hb
    refine ⟨b, hq, fun a => Units.ext ?_⟩
    have h1 := (hWp _ _ _ _ _ (hQ b) (hQ a)).1 (I.isom n hn b a)
    rw [h1, WpPairing.wp_congr_left N hq, NumD.wp_qTor, ← (hQ a).1]
    rfl
  obtain ⟨b, hq, hb⟩ := one t ht
  obtain ⟨b', hq', hb'⟩ := one t' ht'
  refine ⟨b, b', ?_, hb, hb', fun hbb => ?_⟩
  · obtain ⟨z, hz, -⟩ := hq
    refine ⟨ν.eX (-z), ?_⟩
    rw [← (hQ b).1, map_neg, smul_neg, ← map_nsmul, eq_neg_iff_add_eq_zero, ← map_add, ← hz]
    exact map_zero _
  · have h₁ := (G.2.2 _ _ _ _ (hQ b) (hQ b')).1 ((I.ker n hn b b').2 hbb)
    have h₂ := (N.qEq_equivalence n).trans ((N.qEq_equivalence n).trans ((N.qEq_equivalence n).symm hq) h₁) hq'
    obtain ⟨z, hz, hz'⟩ := h₂
    have hz0 : z = 0 := by
      have e : (n : ℤ) • z = 0 := by
        rw [natCast_zsmul]
        have : (0 : N.X) = 0 + n • z := hz
        rw [zero_add] at this
        exact this.symm
      exact (smul_eq_zero.1 e).resolve_left (Int.natCast_ne_zero.2 hn.ne')
    subst hz0
    have e : N.tor (tr t') = N.tor (tr t) := by
      have h := hz'
      rw [NumD.io_zero, _root_.mul_one] at h
      exact h
    have e' := NumD.tor_injective N e
    refine MonoidHom.ext fun χ => ?_
    have := congrArg (fun s : Multiplicative N.X →* Fˣ => s (Multiplicative.ofAdd (ν.eX.symm χ.toAdd))) e'
    simpa [tr] using this.symm

theorem exists_char {X F : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Field F] {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) (S : AddSubgroup X) (x : X) (hx : ∀ s ∈ S, ∀ e, s ≠ x + n • e) :
    ∃ t : Multiplicative X →* Fˣ, t ^ n = 1 ∧ (∀ s ∈ S, t (Multiplicative.ofAdd s) = 1) ∧ t (Multiplicative.ofAdd x) ≠ 1 := by
  let T : AddSubgroup X := S ⊔ (nsmulAddMonoidHom (α := X) n).range
  have hxT : (QuotientAddGroup.mk x : X ⧸ T) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    intro h
    obtain ⟨s, hs, z, ⟨w, rfl⟩, hsz⟩ := AddSubgroup.mem_sup.1 h
    exact hx s hs (-w) (by rw [← hsz, nsmulAddMonoidHom_apply, smul_neg, add_neg_cancel_right])
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hxT
  let g : X →ₗ[ℤ] AddCircle (1 : ℚ) := c ∘ₗ (QuotientAddGroup.mk' T).toIntLinearMap
  have gS : ∀ v ∈ T, g v = 0 := fun v hv => by
    change c (QuotientAddGroup.mk v) = 0
    rw [(QuotientAddGroup.eq_zero_iff v).2 hv, map_zero]
  have gn : ∀ v, n • g v = 0 := fun v => by
    rw [← map_nsmul]
    exact gS _ (AddSubgroup.mem_sup_right ⟨v, rfl⟩)
  let b := Module.Free.chooseBasis ℤ X
  choose r hr using fun i => QuotientAddGroup.mk_surjective (g (b i))
  have hm : ∀ i, ∃ m : ℤ, (m : ℚ) = n * r i := fun i => by
    have := gn (b i)
    rw [← hr i, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, by rw [← nsmul_eq_mul, ← hm, zsmul_eq_mul, _root_.mul_one]⟩
  choose m hm using hm
  let φ : X →ₗ[ℤ] ℚ := b.constr ℤ r
  let ψ : X →ₗ[ℤ] ℤ := b.constr ℤ m
  have hψ : ∀ v, (ψ v : ℚ) = n * φ v := by
    have : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ ψ = (n : ℤ) • φ := b.ext fun i => by
      simp [ψ, φ, hm]
    intro v
    have := congrArg (fun f : X →ₗ[ℤ] ℚ => f v) this
    simpa using this
  have hφ : ∀ v, (QuotientAddGroup.mk (φ v) : AddCircle (1 : ℚ)) = g v := by
    have : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap ∘ₗ φ = g := b.ext fun i => by
      simp [φ, hr]
    intro v
    exact congrArg (fun f : X →ₗ[ℤ] AddCircle (1 : ℚ) => f v) this
  have key : ∀ v, g v = 0 ↔ (n : ℤ) ∣ ψ v := fun v => by
    rw [← hφ, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have : (ψ v : ℚ) = ((n * k : ℤ) : ℚ) := by rw [hψ, ← hk]; push_cast; ring
      exact_mod_cast this
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have := hψ v
      rw [hk] at this
      push_cast at this
      rw [zsmul_eq_mul, _root_.mul_one]
      exact mul_left_cancel₀ hn' this
  let ζu : Fˣ := (hζ.isUnit hn.ne').unit
  have hζu : IsPrimitiveRoot ζu n := IsPrimitiveRoot.coe_units_iff.1 (by simpa [ζu] using hζ)
  let t : Multiplicative X →* Fˣ :=
    { toFun := fun χ => ζu ^ ψ (Multiplicative.toAdd χ)
      map_one' := by simp
      map_mul' := fun a a' => by simp [zpow_add] }
  have tv : ∀ v, t (Multiplicative.ofAdd v) = 1 ↔ (n : ℤ) ∣ ψ v := fun v => hζu.zpow_eq_one_iff_dvd _
  refine ⟨t, MonoidHom.ext fun χ => ?_, fun s hs => (tv s).2 ((key s).1 (gS s (AddSubgroup.mem_sup_left hs))),
    fun h => hc ((key x).2 ((tv x).1 h))⟩
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  change (ζu ^ ψ (Multiplicative.toAdd χ)) ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζu.pow_eq_one, one_zpow]

theorem tateIsoQ_y_cois : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type)
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F),
    ∃ y : ℕ → D.La →ₗ[𝓞 E] D₀.X, (∀ n, 0 < n → ∀ a, ∃ e, y n a = (I.ev n a).y + n • e) ∧
      ∀ n, 0 < n → Cois D (y n) n := by
  intro E _ _ _ H D R _ _ _ _ D₀ _ oa hev hB F _ _ _ _ I
  letI := H.starRing
  haveI := D.proj
  have lift : ∀ n, ∃ y : D.La →ₗ[𝓞 E] D₀.X, 0 < n → ∀ a, ∃ e, y a = (I.ev n a).y + n • e := fun n => by
    by_cases hn : 0 < n
    · have h₁ : ∀ a b, ∃ e, (I.ev n (a + b)).y = (I.ev n a).y + (I.ev n b).y + n • e := fun a b => by
        obtain ⟨q, hq, -, z, hz, -⟩ := I.add n hn a b
        exact ⟨z, by rw [hz, hq]⟩
      have h₂ : ∀ (c : 𝓞 E) a, ∃ e, (I.ev n (c • a)).y = c • (I.ev n a).y + n • e := fun c a => by
        obtain ⟨q, hq, -, z, hz, -⟩ := I.lin n hn c a
        exact ⟨z, by rw [hz, hq]⟩
      obtain ⟨y, hy⟩ := exists_linear_lift (R := 𝓞 E) (M := D.La) n (fun a => (I.ev n a).y) h₁ h₂
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose y hy using lift
  refine ⟨y, hy, fun n hn => ?_⟩
  have hζ : IsPrimitiveRoot ((I.ζ n : Fˣ) : F) n := IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)
  have tv : ∀ t : Multiplicative D₀.X →* Fˣ, t ^ n = 1 → ∀ a,
      t (Multiplicative.ofAdd (I.ev n a).y) = t (Multiplicative.ofAdd (y n a)) := by
    intro t ht a
    obtain ⟨e, he⟩ := hy n hn a
    rw [he, ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, ht, MonoidHom.one_apply, _root_.mul_one]
  have dv : ∀ c : D.La, (∀ a, I.ζ n ^ D.EF c a = 1) → ∃ e, c = n • e := fun c h =>
    exists_nsmul_of_dvd D hn fun a => ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).1 (h a)
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · by_contra hx
    push_neg at hx
    obtain ⟨t, ht, hS, hx'⟩ := exists_char hζ hn (LinearMap.range (y n)).toAddSubgroup x (by
      rintro s ⟨a, rfl⟩ e
      exact hx a e)
    obtain ⟨b, b', -, h1, h2, h3⟩ := torus_pair D D₀ oa hev hB F I n hn t 1 ht (one_pow n)
    obtain ⟨e, he⟩ := dv b fun a => by rw [h1, tv t ht]; exact hS _ ⟨a, rfl⟩
    obtain ⟨e', he'⟩ := dv b' fun a => by rw [h2]; rfl
    exact hx' (by rw [h3 ⟨e - e', by rw [he, he', smul_sub, add_sub_cancel]⟩]; rfl)
  · by_contra hne
    push_neg at hne
    obtain ⟨t, ht, -, hx'⟩ := exists_char hζ hn ⊥ (y n a) (by
      intro s hs e h
      rw [AddSubgroup.mem_bot] at hs
      subst hs
      exact hne (-e) (by rw [smul_neg]; exact eq_neg_of_add_eq_zero_left h.symm))
    obtain ⟨b, -, ⟨e, he⟩, h1, -⟩ := torus_pair D D₀ oa hev hB F I n hn t 1 ht (one_pow n)
    obtain ⟨e', he'⟩ := hy n hn b
    obtain ⟨k, hk⟩ := ha b ⟨e + e', by rw [he', he, smul_add]⟩
    apply hx'
    rw [← tv t ht, ← h1, ef_swap, hk]
    exact ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).2 ⟨-k, by ring⟩

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoSpreadGenericNoetherianDomainStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIso_spread_generic_noetherian_domain : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : Sp R ⟶ Sp o) (z : o) (k : ℕ), 0 < k →
  Module.finrank ℤ D.La = 2 * P.g → ∀ (pt : D.La → (𝟙_ (Over (Sp R)) ⟶ P.A))
  (F : Type) [Field F] [CharZero F] (x₀ : Sp F ⟶ Sp R) (β₀ : o →+* F), DenseRange x₀ → x₀ ≫ s = spMap β₀ →
  ∀ I₀ : TateIso D F (Over.mk x₀ ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
  (I₀.ζ k : F) = β₀ z → (∀ a, toUnit _ ≫ pt a = I₀.ev k a) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ Sp R) (β : o →+* K), x ≫ s = spMap β →
  ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
    (I.ζ k : K) = β z ∧ ∀ a, toUnit _ ≫ pt a = I.ev k a := by
  first | exact @GlobalTheory.LowDat.tateIso_spread | exact GlobalTheory.LowDat.tateIso_spread | (intros; apply GlobalTheory.LowDat.tateIso_spread <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyFormulaNormalCoverRationalThetaConstants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

section Moves

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}

theorem hasTh_of_sabMap (mm : SABMap t' t f) (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S') {N : ℕ}
    (c : Fin N → K) :
    HasTh t'.G t'.PP.L t'.PP.rig m x c ↔ HasTh t.G t.PP.L t.PP.rig m (x ≫ f) c := by
  rw [hasTh_iff, hasTh_iff]
  exact GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen S' t'.G t'.PP.L t'.PP.rig f mm.φ t'.PP.isLB
    t'.PP.rigGen mm.cart (GlobalTheory.ModelSum.lbIso_of_map mm) m m N N K x c c

theorem polFib_of_sabMap (mm : SABMap t' t f) (g : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S') :
    PolFib t'.G t'.PP.L g x ↔ PolFib t.G t.PP.L g (x ≫ f) :=
  (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S' t.G t.PP.L t'.G t'.PP.L f mm.φ t.PP.isLB t'.PP.isLB mm.cart
    (GlobalTheory.ModelSum.lbIso_of_map mm) g R x).1

end Moves

end GlobalTheory.UMin

namespace GlobalTheory.UMin

open GlobalTheory.CechPic in

theorem key_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (π : M.Z ⟶ Y.X) (y : Sp Ω ⟶ Xo.XF c) (d : Fin (n + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ π = y ≫ Y.j → HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (y ≫ pullback.fst _ _) d → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) 8).pull π) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial)).pull π) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf Y g hYg Ω _ _ _ M π y d hZ hpt hth
  obtain ⟨t, ⟨mt⟩⟩ := GlobalTheory.ModelSum.exists_pull π Y.t
  have hP : PCrd (M.pt ≫ (π ≫ g)) (symTup d) := by
    have h1 : M.pt ≫ (π ≫ g) = y ≫ f := by rw [← Category.assoc, hpt, Category.assoc, hYg]
    rw [h1]; exact hf Ω y d hth
  have hD : M.HasDiv d :=
    GlobalTheory.T.hasDiv_of_hasDiv_thetaSymmetricFunctionsDegreeFactorial c.F Ω M (n + 1) d hZ (GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords c.F Ω o M n (π ≫ g) (symTup d) hP)
  obtain ⟨h, -, hhP⟩ := GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv c.F Ω M n d hD
  have hsym := GlobalTheory.T.symmetric_coordinates_O1_factorial_power c.F Ω o M n h (π ≫ g) d hhP hP
  have hThO : HasTh Y.oF.t.G Y.oF.t.PP.L Y.oF.t.PP.rig m y d := (hasTh_of_sabMap Y.m0.toSABMap m y d).2 hth
  have hThY : HasTh Y.t.G Y.t.PP.L Y.t.PP.rig m (M.pt ≫ π) d := by
    rw [hpt]; exact (hasTh_of_sabMap Y.m m y d).1 hThO
  have hTh : HasTh t.G t.PP.L t.PP.rig m M.pt d := (hasTh_of_sabMap mt m M.pt d).2 hThY
  have hPolO : PolFib Y.oF.t.G Y.oF.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) y :=
    (polFib_of_sabMap Y.m0.toSABMap _ y).2 (GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c Ω _)
  have hPolY : PolFib Y.t.G Y.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (M.pt ≫ π) := by
    rw [hpt]; exact (polFib_of_sabMap Y.m _ y).1 hPolO
  have hPol : PolFib t.G t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) M.pt := (polFib_of_sabMap mt _ M.pt).2 hPolY
  have hmk : IsUnit (m : c.F) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by omega))
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.theta_coordinates_section_exists E H c.F Ω M t _ m n d h hZ hm hm3 hmk hPol hTh hhP
  obtain ⟨hab, hop, hamp⟩ := GlobalTheory.T.abelianLocus_eq_preimage_moduli_and_principal E H Dw l Xo c Y M.Z π t ⟨mt⟩
  obtain ⟨hsmY, hvY⟩ := GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y
  have hsm : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback mt.cart.1 hsmY
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have hne : ((⊤ : M.Z.Opens) : Set M.Z).Nonempty := ⟨M.pt (IsLocalRing.closedPoint Ω), trivial⟩
  haveI : CharZero Γ(M.Z, ⊤) := (M.res ⊤ hne).charZero
  have hne2 : (abLocus t.G).Nonempty := by
    refine ⟨M.pt (IsLocalRing.closedPoint Ω), ?_⟩
    rw [hab]
    show π (M.pt (IsLocalRing.closedPoint Ω)) ∈ Set.range Y.j
    have hq := congrArg (fun φ : Sp Ω ⟶ Y.X => φ (IsLocalRing.closedPoint Ω)) hpt
    exact ⟨y (IsLocalRing.closedPoint Ω), hq.symm⟩
  have hδ : ((ProjSpace.O1 c.F n).pull h).IsLB := pull_isLB (ProjSpace.O1_isLB c.F n) h
  have := Y.t.semi.separated
  have hHY := hvY.isLB_det
  have hHt := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback mt.cart hvY).isLB_det
  have hkey : LBIso (lbPow ((ProjSpace.O1 c.F n).pull h) 8)
      (lbPow (GlobalTheory.SiegelTor.hodge t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) 4) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) with h0 | h0
    · have hn0 : n = 0 := by
        rw [h0] at hn
        simpa using hn
      subst hn0
      refine (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).1 ?_
      have hz : cls _ hHt = 0 := by
        revert hHt
        rw [h0]
        exact fun hHt => KeySmall.cls_det_zero _ hHt
      rw [cls_lbPow hδ, cls_lbPow hHt, hz, cls_pull (ProjSpace.O1_isLB c.F 0), KeySmall.cls_O1_zero, map_zero,
        nsmul_zero, nsmul_zero]
    · refine KeySmall.key_sab M.Z t _ _ σ h0 hZ inferInstance inferInstance (fun A _ ξ hξ => ?_) hsm hne2 hop hδ hamp
        (KeySmall.nzFib_of_geom σ hσ)
      exact KeySmall.mk_le_of_lft ((Cardinal.mk_le_of_injective (f := fun a : c.F => (a : ℂ)) Subtype.val_injective).trans_eq
        Cardinal.mk_complex) (ξ ≫ M.s)
  have hO := ProjSpace.O1_isLB o n
  have e1 := (cls_eq_iff (pull_isLB hO (π ≫ g)) (isLB_lbPow hδ _)).2 hsym
  have e2 := (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).2 hkey
  have e3 := (cls_eq_iff (pull_isLB hHY π) hHt).2 (GlobalTheory.HodgeGenDesc.lbIso_hodge_pull mt.cart hvY)
  rw [cls_pull hO, pull_comp, cls_lbPow hδ] at e1
  rw [cls_lbPow hδ, cls_lbPow hHt] at e2
  rw [cls_pull hHY] at e3
  refine (cls_eq_iff (pull_isLB (isLB_lbPow (pull_isLB hO g) 8) π) (pull_isLB (isLB_lbPow hHY _) π)).1 ?_
  rw [cls_pull (isLB_lbPow (pull_isLB hO g) 8), cls_pull (isLB_lbPow hHY _), cls_lbPow (pull_isLB hO g),
    cls_lbPow hHY, map_nsmul, map_nsmul, cls_pull hO, e1, e3, smul_smul, mul_comm 8, ← smul_smul, e2, smul_smul,
    mul_comm]

end GlobalTheory.UMin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfLatticeValueStatementsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPeriodZeta_of_latticeValue_statements : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatVal.LatIntRam → GlobalTheory.LatVal.LatIntUnr → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  first | exact @GlobalTheory.JoinFun.joinOut_of_lat | exact GlobalTheory.JoinFun.joinOut_of_lat | (intros; apply GlobalTheory.JoinFun.joinOut_of_lat <;> assumption)
end

