import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModTSupConj
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem modT_sup_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (t : T),
    modT G t ⊔ D.host.conj • modT G t = ⊤ := by
  intro D T L sc μ₀ hL G t
  classical
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hund : ∀ PP PP' : HeightOneSpectrum (𝓞 D.host.E), PP.asIdeal = D.host.conj • PP'.asIdeal →
      PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) := by
    intro PP PP' h
    have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv PP' PP := by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      intro x y hxy
      have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
      rw [hy, h]
      exact Ideal.smul_mem_pointwise_smul_iff.symm
    exact (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) PP' PP).2
      (Or.inr hc)
  have hmax' : ∀ PP : HeightOneSpectrum (𝓞 D.host.E), (D.host.conj • PP.asIdeal).IsMaximal := by
    intro PP
    have := PP.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => PP.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have hmem : ∀ w ∈ twPl G t, w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
    intro w hw
    rw [twPl, Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union] at hw
    exact ⟨hw.1.resolve_left hw.2, hw.2⟩
  have hoff : ∀ w ∈ twPl G t, w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro w hw hS
    obtain ⟨hQ, hW⟩ := hmem w hw
    rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
    · exact G.pl.levelPlace_ne_basePlace t w hQ h0
    · apply hW
      rw [G.pl.w_Q t w hQ h1]
      exact Finset.mem_image_of_mem _ hS
  have hAB : ∀ v ∈ G.pl.S0, ∀ w ∈ twPl G t, (G.pl.w v).asIdeal ≠ D.host.conj • w.asIdeal := by
    intro v hv w hw h
    exact hoff w hw (by rw [← hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBA : ∀ w ∈ twPl G t, ∀ v ∈ G.pl.S0, w.asIdeal ≠ D.host.conj • (G.pl.w v).asIdeal := by
    intro w hw v hv h
    exact hoff w hw (by rw [hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBB : ∀ w ∈ twPl G t, ∀ w' ∈ twPl G t, w.asIdeal ≠ D.host.conj • w'.asIdeal := by
    intro w hw w' hw' h
    refine (hL.Q_pl t w' (hmem w' hw').1).2 w (hmem w hw).1 fun c hc => ⟨D.host.conj • c, ?_, ?_⟩
    · rw [h]; exact Ideal.smul_mem_pointwise_smul _ _ _ hc
    · exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [modT, smul_mul', ← Ideal.isCoprime_iff_sup_eq]
  refine IsCoprime.mul_left (IsCoprime.mul_right ?_ ?_) (IsCoprime.mul_right ?_ ?_) <;> rw [Ideal.isCoprime_iff_sup_eq]
  · exact condE_sup_conj G.pl
  · rw [Finset.smul_prod']
    refine Ideal.prod_sup_eq_top fun v hv => Ideal.sup_prod_eq_top fun w hw => ?_
    exact Ideal.pow_sup_eq_top (Ideal.IsMaximal.coprime_of_ne (G.pl.w v).isMaximal (hmax' w) (hAB v hv w hw))
  · rw [GlobalTheory.FunObj.SqNum.condE, Finset.smul_prod']
    simp only [smul_pow']
    refine Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun v hv => ?_
    exact Ideal.sup_pow_eq_top (Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' _) (hBA w hw v hv))
  · rw [Finset.smul_prod']
    exact Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun w' hw' =>
      Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' w') (hBB w hw w' hw')

end GlobalTheory.SqTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismOpenAffineLineAbelianSchemeConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NoRatCurve

section
variable (k : Type) [Field k] (P : Polynomial k)

def rhoMap : Localization.Away (Polynomial.X : Polynomial k) →+* Localization.Away (Polynomial.X * P) :=
  IsLocalization.Away.awayToAwayRight (S := Localization.Away (Polynomial.X : Polynomial k))
    (P := Localization.Away (Polynomial.X * P)) (Polynomial.X : Polynomial k) P

theorem rhoMap_algebraMap (x : Polynomial k) :
    rhoMap k P (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) x) =
      algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) x :=
  IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away (Polynomial.X : Polynomial k))
    (P := Localization.Away (Polynomial.X * P)) _ _ x

theorem rhoMap_invSelf : rhoMap k P (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)) =
    algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
      IsLocalization.Away.invSelf (Polynomial.X * P) := by
  have hu1 : IsUnit (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X) :=
    isUnit_of_mul_isUnit_left (x := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X)
      (y := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P)
      (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _)
  apply hu1.mul_left_cancel
  calc _ = rhoMap k P (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)) := by rw [map_mul, rhoMap_algebraMap]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := by rw [← _root_.mul_assoc, ← map_mul, IsLocalization.Away.mul_invSelf]

theorem rhoMap_comp_algebraMap : (rhoMap k P).comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) =
    algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) :=
  RingHom.ext (rhoMap_algebraMap k P)

theorem rhoMap_comp_aeval : (rhoMap k P).comp (Polynomial.aeval (R := k) (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
      Localization.Away (Polynomial.X : Polynomial k))).toRingHom =
    (Polynomial.aeval (R := k) (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
      IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have e1 : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))) (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) (Polynomial.C a) := by
      rw [Polynomial.aeval_C]; rfl
    have e2 : (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
        IsLocalization.Away.invSelf (Polynomial.X * P))) (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) (Polynomial.C a) := by
      rw [Polynomial.aeval_C]; rfl
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e1, e2,
      rhoMap_algebraMap]
  · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X, Polynomial.aeval_X]
    exact rhoMap_invSelf k P

end

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem awayToAwayRight_injective (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    Function.Injective (rhoMap k P) := by
  have hXP : (Polynomial.X * P : Polynomial k) ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hP
  have hinj : Function.Injective (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P))) :=
    IsLocalization.injective (Localization.Away (Polynomial.X * P)) (powers_le_nonZeroDivisors_of_noZeroDivisors hXP)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (Polynomial.X : Polynomial k)) z
  have e := rhoMap_algebraMap k P a
  have h1 : IsLocalization.mk' (Localization.Away (Polynomial.X : Polynomial k)) a s *
      algebraMap _ _ (s : Polynomial k) = algebraMap _ _ a := IsLocalization.mk'_spec _ _ _
  have h2 := congrArg (rhoMap k P) h1
  rw [map_mul, hz, zero_mul, e] at h2
  have ha : a = 0 := hinj (by rw [← h2, map_zero])
  subst ha
  simp

theorem extend_to_line : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k), P ≠ 0 → ∀ u : Sp (Localization.Away P) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → ∃ v : Sp (Polynomial k) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Polynomial k)) ∧ spMap (algebraMap (Polynomial k) (Localization.Away P)) ≫ v = u := by
  intro k _ _ B _ _ P hP
  induction hn : P.natDegree generalizing P with
  | zero =>
    intro u hu
    obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.1 hn
    have ha : IsUnit (Polynomial.C a) := Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 (by rintro rfl; simp at hP))
    let φ : Localization.Away (Polynomial.C a) →+* Polynomial k := IsLocalization.Away.lift (g := RingHom.id (Polynomial k)) (Polynomial.C a) ha
    have hφ : (algebraMap (Polynomial k) (Localization.Away (Polynomial.C a))).comp φ = RingHom.id _ :=
      IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.C a)) (RingHom.ext fun x => by
        simp [φ, IsLocalization.Away.lift, IsLocalization.lift_eq])
    refine ⟨spMap φ ≫ u, ?_, ?_⟩
    · rw [Category.assoc, hu, ← spMap_comp']
      congr 1
      refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (Polynomial.C a))]
      simp [φ, IsLocalization.Away.lift, IsLocalization.lift_eq]
    · rw [← Category.assoc, ← spMap_comp', hφ]
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ u = u
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  | succ n ih =>
    intro u hu
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root P (by rw [Polynomial.degree_eq_natDegree hP, hn]; exact_mod_cast Nat.succ_ne_zero n)
    obtain ⟨P', rfl⟩ : ∃ P', P = P' * (Polynomial.X - Polynomial.C c) :=
      ⟨P /ₘ (Polynomial.X - Polynomial.C c), by rw [mul_comm, Polynomial.mul_divByMonic_eq_iff_isRoot.2 hc]⟩
    have hP' : P' ≠ 0 := left_ne_zero_of_mul hP
    have hn' : P'.natDegree = n := by
      rw [Polynomial.natDegree_mul hP' (Polynomial.X_sub_C_ne_zero c), Polynomial.natDegree_X_sub_C] at hn
      omega
    obtain ⟨v', hv', ev'⟩ := GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point k B P' c hP' u hu
    obtain ⟨v, hv, ev⟩ := ih P' hP' hn' v' hv'
    refine ⟨v, hv, ?_⟩
    rw [← ev', ← ev, ← Category.assoc, ← spMap_comp']
    congr 2
    exact RingHom.ext fun x => (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away P')
      (P := Localization.Away (P' * (Polynomial.X - Polynomial.C c))) P' (Polynomial.X - Polynomial.C c) x).symm

theorem maps_from_open_line_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ B.left) (a b : Localization.Away P →ₐ[k] k), u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u = spMap b.toRingHom ≫ u := by
  intro k _ _ B _ hB P hP u a b hu
  haveI := hB.smooth
  haveI := hB.proper
  obtain ⟨Q, hQ, σ, τ, h1, h2⟩ := GlobalTheory.T.exists_inversion_coordinate_localization_polynomial k P hP
  obtain ⟨f₀, hf₀, e₀⟩ := extend_to_line k B P hP u hu
  have hu' : (spMap σ.toRingHom ≫ u) ≫ B.hom = spMap (algebraMap k (Localization.Away Q)) := by
    rw [Category.assoc, hu, ← spMap_comp']
    congr 1
    ext x
    exact σ.commutes x
  obtain ⟨f₁, hf₁, e₁⟩ := extend_to_line k B Q hQ _ hu'
  haveI : IsDominant (spMap (rhoMap k P)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (rhoMap k P))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (awayToAwayRight_injective k P hP)]
    exact bot_le
  have hc : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ := by
    refine ext_of_isDominant_of_isSeparated B.hom ?_ (spMap (rhoMap k P)) ?_
    · rw [Category.assoc, Category.assoc, hf₀, hf₁, ← spMap_comp', ← spMap_comp']
      congr 1
      refine RingHom.ext fun x => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    · calc spMap (rhoMap k P) ≫ spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀
          = spMap ((rhoMap k P).comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))) ≫ f₀ := by
            rw [spMap_comp' (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (rhoMap k P),
              Category.assoc]
        _ = spMap τ.toRingHom ≫ spMap σ.toRingHom ≫ u := by
            rw [rhoMap_comp_algebraMap, ← h1, spMap_comp', Category.assoc, e₀]
            show spMap (τ.toRingHom.comp σ.toRingHom) ≫ u = _
            rw [spMap_comp', Category.assoc]
        _ = spMap (τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q))) ≫ f₁ := by
            rw [spMap_comp', Category.assoc, e₁]
        _ = _ := by
            rw [h2, ← rhoMap_comp_aeval, spMap_comp', Category.assoc]
  have key := GlobalTheory.T.projectiveLine_to_abelianVariety_const k B hB f₀ f₁ hf₀ hf₁ hc
    (a.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P)))
    (b.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P)))
  rw [← e₀, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp']
  exact key

end GlobalTheory.NoRatCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CMVal GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.ChiGrid

namespace GlobalTheory.SqTop.FieldDatPf

theorem good_prime {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (hs : GlobalTheory.Mem.Chr.SplitsC H.E p) :
    ¬ (p : ℤ) ∣ discr H.E ∧ ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal →
      Ideal.absNorm P.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below P) := by
  refine ⟨GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp _ ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver hp).symm.trans hs),
    fun P hP => ?_⟩
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs P hP
  exact ⟨h1, GlobalTheory.ToricDenom.splits_below H h3⟩

theorem splitsC_of_mod {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (h : p % (H.QS * H.q * H.d) = 1) :
    GlobalTheory.Mem.Chr.SplitsC H.E p :=
  (GlobalTheory.HostSplit.split_of_one_mod R H p hp h).1

theorem exists_above {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (OF E)) :
    ∃ P : HeightOneSpectrum (𝓞 E), GlobalTheory.ToricDenom.below P = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, hv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  exact ⟨⟨Q, hQ.isPrime, hne⟩, HeightOneSpectrum.ext hv.over.symm⟩

theorem natCast_mem_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : OF E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal ↔ (n : 𝓞 E) ∈ P.asIdeal := by
  show algebraMap (OF E) (𝓞 E) _ ∈ P.asIdeal ↔ _
  rw [map_natCast]

variable {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T}

open Classical in

theorem expIn_condF' (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    expIn (condF P) v = if v ∈ P.S0 then condExp P v else 0 := by
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), v ∉ S →
      ¬ v.asIdeal ∣ ∏ u ∈ S, u.asIdeal ^ condExp P u := fun S hS h => by
    obtain ⟨u, hu, h⟩ := (v.prime.dvd_finset_prod_iff _).1 h
    have h2 := v.prime.dvd_of_dvd_pow h
    have : v = u := HeightOneSpectrum.ext (associated_iff_eq.1 (v.irreducible.associated_of_dvd u.irreducible h2))
    exact hS (this ▸ hu)
  show multiplicity v.asIdeal (∏ u ∈ P.S0, u.asIdeal ^ condExp P u) = _
  split_ifs with h
  · rw [← Finset.mul_prod_erase _ _ h]
    refine multiplicity_eq_of_dvd_of_not_dvd (dvd_mul_right _ _) fun h' => ?_
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ v.ne_bot)] at h'
    exact key _ (Finset.notMem_erase _ _) h'
  · exact multiplicity_eq_zero.2 (key _ h)

theorem isBaseCond_condF (P : Places L) (hg : ∀ i, D.host.g i % LevelStarExponents.condE D = 1)
    (hpde : ((Ideal.span {(D.host.pde : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
      ((Ideal.span {(D.host.pde' : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E) :
    IsBaseCond (condF P) := by
  classical
  have hE : 1 < LevelStarExponents.condE D := by
    have := D.host.qd_big
    unfold LevelStarExponents.condE
    have h1 : 1 ≤ D.host.QS := D.host.QS_pos
    have h2 : 1 < D.host.q := by omega
    have h3 : 1 ≤ D.host.d := by omega
    calc 1 < 1 * D.host.q * 1 := by omega
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr

  have hgood : ∀ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) →
      p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
        (p : 𝓞 D.host.E) ∈ Q.asIdeal → Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
    have ofMod : ∀ p : ℕ, p.Prime → p % LevelStarExponents.condE D = 1 → p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
        ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal →
          Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
      intro p hp hm
      have h4 : p % 4 = 1 := by
        have : (4 : ℕ) ∣ LevelStarExponents.condE D := ((dvd_trans (by norm_num) (UpperTheory.Ram.Rd.sixteen_dvd_QS D.host)).mul_right _).mul_right _
        rw [← Nat.mod_mod_of_dvd p this, hm]
      refine ⟨hp, by omega, good_prime D.host hp (splitsC_of_mod D.host hp hm)⟩
    have ofSplit : ∀ p : ℕ, p.Prime → p % 15 = 1 →
        ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E →
        p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
        ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal →
          Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
      intro p hp h15 hs
      have hs' : GlobalTheory.Mem.Chr.SplitsC D.host.E p := by
        have e := GlobalTheory.HostSplit.ncard_placesOver D.host.E hp
        rw [hs] at e
        exact e
      exact ⟨hp, by omega, good_prime D.host hp hs'⟩
    rintro p (rfl | rfl | rfl | rfl | rfl)
    · exact ofMod _ (D.host.g_prime 0) (hg 0)
    · exact ofMod _ (D.host.g_prime 1) (hg 1)
    · exact ofSplit _ D.host.pde_prime D.host.pde_mod.1 hpde.1
    · exact ofSplit _ D.host.pde'_prime D.host.pde_mod.2 hpde.2
    · obtain ⟨hq, hqm, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
      refine ofMod _ hq ?_
      rw [← Nat.mod_mod_of_dvd _ (dvd_mul_left (LevelStarExponents.condE D) (Formalism.MainNotions.rPrAv D)), hqm]
      exact Nat.mod_eq_of_lt hE
  have hexp : ∀ v : HeightOneSpectrum (OF D.host.E), v.asIdeal ∣ condF P → v ∈ P.S0 := by
    intro v hv
    by_contra h
    have e := expIn_condF' P v
    rw [if_neg h] at e
    have := multiplicity_eq_zero.1 e
    exact this hv
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ v.ne_bot
  · intro e
    have h0 : P.v0 ∈ P.S0 := P.mem_S0_of_sum_eq.2 (Or.inl rfl)
    have e1 := expIn_condF' P P.v0
    rw [if_pos h0, condExp, if_pos rfl] at e1
    have e2 : expIn (condF P) P.v0 = 0 := by
      rw [e]; exact multiplicity_eq_zero.2 fun h => P.v0.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
    omega
  · have hS := hexp v hv
    have hle : expIn (condF P) v ≤ 2 := by
      rw [expIn_condF', if_pos hS, condExp]; split_ifs <;> omega
    obtain ⟨p, hp, hpv⟩ : ∃ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) ∧
        (p : OF D.host.E) ∈ v.asIdeal := by
      rcases P.mem_S0_of_sum_eq.1 hS with h | h
      · exact ⟨q0 D, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h ▸ P.basePlace_over_qZero⟩
      · rcases (S1_mem_OmF D).1 h with h | h | h | h
        · exact ⟨_, Or.inl rfl, h⟩
        · exact ⟨_, Or.inr (Or.inl rfl), h⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩
    obtain ⟨h1, h2, h3, h4⟩ := hgood p hp
    obtain ⟨Q, rfl⟩ := exists_above v
    exact ⟨(h4 Q ((natCast_mem_below Q p).1 hpv)).2, hle, p, h1, h2, hpv, h3, fun Q' hQ' => (h4 Q' hQ').1⟩

theorem isCMType_cmPhi (D : D7) : IsCMType (cmPhi D) ∧ ∀ τ τ', cmPhi D τ D.host.sqrtMinusD = cmPhi D τ' D.host.sqrtMinusD := by
  obtain ⟨hcm, hsq⟩ := GlobalTheory.LamTie.CMType.phi_cmType D.R D.host
  have e : ∀ τ, cmPhi D τ = GlobalTheory.LamTie.phi D.host (D.eTau τ) := fun _ => rfl
  refine ⟨fun σ => ?_, fun τ τ' => by rw [e, e]; exact hsq _ _⟩
  obtain ⟨g, hg, hu⟩ := hcm σ
  refine ⟨D.eTau.symm g, ?_, fun τ hτ => ?_⟩
  · simp only [e, Equiv.apply_symm_apply]
    exact hg
  · have hτ' : σ = GlobalTheory.LamTie.phi D.host (D.eTau τ) ∨ σ = ComplexEmbedding.conjugate (GlobalTheory.LamTie.phi D.host (D.eTau τ)) := by
      simpa only [e] using hτ
    rw [← hu _ hτ', Equiv.symm_apply_apply]

end GlobalTheory.SqTop.FieldDatPf

namespace GlobalTheory.SqTop

theorem fieldDat : FieldDat := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ _ G => ?_⟩⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  obtain ⟨hcm, hsq⟩ := FieldDatPf.isCMType_cmPhi D
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  exact ⟨D.host.isCMField_hostE, GlobalTheory.ToricDenomBridge.host_isAbelianGalois D.host,
    GlobalTheory.ToricDenomBridge.isFieldData_host D.host hcm hsq, FieldDatPf.isBaseCond_condF G.pl Pm.g_mod Pm.pde_split,
    GlobalTheory.ToricDenom.ringPair D.host.d hd,
    GlobalTheory.ToricDenomBridge.isIntLattice_of D.host.hyp.2.1 (by have := D.host.hyp.2.2.2.1; omega) rfl rfl⟩

end GlobalTheory.SqTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc}

def IsStageC (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  p ≤ pp D j ∧ q ≤ qq D j ∧ A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p ∧
    A'.rank + 2 * qq D j = rankV D i j + 2 * q ∧ NegIdx A p ∧ NegIdx A' q ∧ NegIdx WW (p + q) ∧
    X.Is W.ψ W.θ (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (fun t => nuH G t i j) (locPl G)

theorem negIdx_of_isStd {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) : NegIdx V 0 := fun τ => by
  have : gramAt D V τ = 1 := by rw [gramAt, h.1]; simp
  rw [this]
  refine ⟨(Equiv.sumEmpty _ _).symm, 1, ?_⟩
  ext (a | a) (b | b)
  · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
  all_goals first | exact a.elim0 | exact b.elim0

theorem IsBottomTri.isStageC {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsBottomTri W i j X) : IsStageC W i j 0 0 X := by
  have r := ranks_exact D i j
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, negIdx_of_isStd h.std, negIdx_of_isStd h.std',
    negIdx_of_isStd h.stdW, h.is⟩
  · rw [h.rank]; simpa [pp] using r.1
  · rw [h.rank']; simpa [qq] using r.2.1

end GlobalTheory.SqTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsBijectiveOfParts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.PrimIn

theorem principalLevel_rows_bijective_of_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → R.PrincipalLevelBijective F := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hOk hW hUp hRow hIn
  have hinj := GlobalTheory.T.injective_complexCoords_principalLevel R F hOk hW hIn
  have htop := GlobalTheory.T.complexCoords_principalLevel_range_eq_top R F hOk hW hUp hRow hIn
  refine ⟨hinj _, fun t => ⟨hinj t, ?_⟩⟩
  rw [htop t, htop _]

end GlobalTheory.PrimIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAcyclicOfCechVanishingAllCoversStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativelyAcyclic_of_cech_vanishing_all_covers : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (P : LB A.left), (∀ j : ℕ, ¬ NV A P (j + 1)) → GlobalTheory.CxForm.IsRelAcyclic A.hom A.hom P := by
  first | exact @GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV | exact GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV | (intros; apply GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV <;> assumption)
end

