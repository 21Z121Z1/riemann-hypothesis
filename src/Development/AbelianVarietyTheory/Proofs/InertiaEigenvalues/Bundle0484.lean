import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0386
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0390
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0394
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountOfSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLSaturatedOfSelmerSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultisetBaseLatticeEqJumpsMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootEqOfNormSubLtOne
section
namespace GlobalTheory.UltrametricUnitNorm

section
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_add_lt_one {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_pow_sub_one_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (i : ℕ) : ‖u ^ i - 1‖ < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
    rw [e]
    refine norm_add_lt_one ?_ h
    rwa [norm_mul, hu, one_mul]

theorem norm_geom_sub_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (n : ℕ) :
    ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact norm_add_lt_one ih (norm_pow_sub_one_lt hu h n)

omit [IsUltrametricDist K] in
theorem norm_eq_one_of_pow {x : K} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : ‖x‖ = 1 := by
  have h : ‖x‖ ^ m = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 h

theorem eq_of_norm_sub_lt {m : ℕ} (hm : 0 < m) (hn : ‖(m : K)‖ = 1) {ζ η : K} (hζ : ζ ^ m = 1)
    (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  have nζ := norm_eq_one_of_pow hm hζ
  have nη := norm_eq_one_of_pow hm hη
  have z0 : ζ ≠ 0 := by
    rintro rfl
    simp at nζ
  by_contra hne
  have hu : ‖η / ζ‖ = 1 := by rw [norm_div, nζ, nη, div_one]
  have hu1 : η / ζ - 1 = (η - ζ) / ζ := by field_simp
  have hlt : ‖η / ζ - 1‖ < 1 := by rwa [hu1, norm_div, nζ, div_one]
  have hne' : η / ζ - 1 ≠ 0 := by
    rw [hu1]
    exact div_ne_zero (sub_ne_zero.2 hne) z0
  have hs : (∑ i ∈ Finset.range m, (η / ζ) ^ i) = 0 := by
    have := geom_sum_mul (η / ζ) m
    rw [div_pow η ζ m, hη, hζ, div_one, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne'
  have := norm_geom_sub_lt hu hlt m
  rw [hs, zero_sub, norm_neg, hn] at this
  exact lt_irrefl _ this

end

theorem norm_natCast_eq_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hlm : ¬l ∣ m) :
    ‖(m : PadicAlgCl l)‖ = 1 := by
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := (map_natCast _ m).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm

theorem root_eq_of_norm_sub_lt_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hm : 0 < m) (hlm : ¬l ∣ m)
    {ζ η : Formalism.BasicNotions.Loc.Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ :=
  eq_of_norm_sub_lt hm (norm_natCast_eq_one hlm) hζ hη h

end GlobalTheory.UltrametricUnitNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerOrderFormulaDualSelmer
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.SelOrder

theorem cupB_sub_cob {Γ A M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
    {n : ℕ} (χ : Γ → ZMod n) (π : Representation A Γ M) (π' : Representation A Γ M') (P : M →+ M' →+ ZMod n)
    (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x : Γ → M) (y y' : Γ → M') (m : M')
    (hx : Continuous x) (hx' : ∀ g h, x (g * h) = x g + π g (x h)) (hm : Continuous fun g => π' g m)
    (hy : ∀ g, y' g = y g - (π' g m - m))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x y' := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P (x g) (π' g m), hF.add (((IsLocallyConstant.iff_continuous _).2 (hx.prodMk hm)).comp
    fun p : M × M' => P p.1 p.2), fun g k => ?_⟩
  have h1 := h g k
  have h2 := hP g (x k) (π' k m)
  simp only [hy, map_add, map_sub, AddMonoidHom.add_apply, Pi.add_apply, hx', map_mul, Module.End.mul_apply] at h1 ⊢
  linear_combination h1 + h2

theorem tors_all (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (B : Type) [AddCommGroup B] [Module A B] :
    Tors A B := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine fun b => ⟨n, fun x hx => ?_⟩
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

section General

open Formalism.GaloisCohomology

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] (n : ℕ) {Λ W W' : Type} [CommRing Λ]
  [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W]
  [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W']

theorem order_formula (hPT : PoitouTateTotallyComplex) (hLF : LocalFiniteness) (hLD : LocalTateDuality)
    (hLE : LocalEulerChar) (hGF : GlobalFiniteness) (hGE : GlobalEulerChar)
    (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)) (hn : 0 < n)
    (hc : ContAction ρ) (hc' : ContAction ρ') (hl : ∀ x, (∀ y, P x y = 0) → x = 0) (hr : ∀ y, (∀ x, P x y = 0) → y = 0)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y)
    (A : Places F Ω) (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (hTl : ∀ v ∈ T, v ∉ placesOver F l) (hQl : ∀ v ∈ Q, v ∉ placesOver F l)
    (hur : ∀ v, v ∉ placesOver F l → v ∉ T → v ∉ Q → ∀ B : ValuationSubring Ω, IsPlaceOver B v →
      ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1)
    (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (C : Set (H1 ρ'))
    (hC : ∀ c, c ∈ C ↔ ∃ y : Z1 ρ',
      ((∀ v, v ∉ placesOver F l → v ∉ T → v ∉ Q → ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧
        (∀ v, v ∈ T ∨ v ∈ Q → ∃ m, ∀ g ∈ Dec (F := F) (A.1 v), y.1 g = ρ' g m - m) ∧
        ∀ v ∈ placesOver F l, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v →
          CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
            (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) ∧ c = Submodule.Quotient.mk y)
    (h0 : H0 ρ = ⊥) (h0' : H0 ρ' = ⊥) (hT0 : ∀ v ∈ T, H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype) = ⊥)
    (hcount : ∏ᶠ v ∈ placesOver F l, Nat.card (L v) =
      (∏ᶠ v ∈ placesOver F l, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
        Nat.card W ^ InfinitePlace.nrComplexPlaces F) :
    Finite C ∧ Nat.card (SelAll ρ A (bkCond ρ A l (T ∪ ↑Q) L)) =
      Nat.card C * ∏ v ∈ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) := by
  classical
  have hfin := GlobalTheory.SelObstruction.finite_above (F := F) l
  have hsub : ∀ {M : Type} [AddCommGroup M] [Module Λ M] [TopologicalSpace M] [DiscreteTopology M]
      (π : Representation Λ (G F Ω) M), ContAction π → ∀ U : Subgroup (G F Ω), ContAction (π.comp U.subtype) :=
    fun π h U => h.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hloc := fun v => GlobalTheory.T.localDuality_perfect_pair_finite_modules hLF hLD hLE F Ω l n (A.1 v) v (A.2 v) Λ W W'
    (ρ.comp (Dec (F := F) (A.1 v)).subtype) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P hn (hsub ρ hc _) (hsub ρ' hc' _)
    hl hr (fun g x y => hP g.1 x y)
  have hS : ∀ v, v ∈ hfin.toFinset ∪ (hT.toFinset ∪ Q) ↔ v ∈ placesOver F l ∨ v ∈ T ∨ v ∈ Q := by simp
  have hS' : ∀ v, v ∉ hfin.toFinset ∪ (hT.toFinset ∪ Q) ↔ v ∉ placesOver F l ∧ v ∉ T ∧ v ∉ Q := fun v => by
    rw [hS, not_or, not_or]
  have hnl : ∀ v, v ∈ T ∨ v ∈ Q → v ∉ placesOver F l := fun v h => h.elim (hTl v) (hQl v)
  have b1 : ∀ v ∈ placesOver F l, bkCond ρ A l (T ∪ ↑Q) L v = L v := fun v hv => if_pos hv
  have b2 : ∀ v, v ∈ T ∨ v ∈ Q → bkCond ρ A l (T ∪ ↑Q) L v = ⊤ := fun v hv => (if_neg (hnl v hv)).trans (if_pos hv)
  obtain ⟨fC, e⟩ := GlobalTheory.T.greenbergWiles_pair_alt hPT hLF hGF hGE F Ω l n Λ W W' ρ ρ' P hn hc hc' hl hr hP
    (hfin.toFinset ∪ (hT.toFinset ∪ Q)) A (fun v hv => (hS v).2 (.inl hv))
    (fun v hv => hur v ((hS' v).1 hv).1 ((hS' v).1 hv).2.1 ((hS' v).1 hv).2.2) (bkCond ρ A l (T ∪ ↑Q) L)
    (fun v hv => (if_neg ((hS' v).1 hv).1).trans (if_neg (not_or.2 ((hS' v).1 hv).2))) C (fun y => by
      rw [hC]
      constructor
      · rintro ⟨y', ⟨k1, k2, k3⟩, e⟩
        have e' : (y' - y).1 ∈ B1 ρ' := (Submodule.Quotient.eq ((B1 ρ').comap (Z1 ρ').subtype)).1 e.symm
        obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 e'
        have hm' : ∀ g, y.1 g = y'.1 g - (ρ' g m - m) := fun g => by
          rw [← hm g]
          exact (sub_sub_cancel _ _).symm
        refine ⟨fun v hv τ hτ => ?_, fun v hv x hx => ?_⟩
        · obtain ⟨a, b, c⟩ := (hS' v).1 hv
          rw [hm', k1 v a b c τ hτ, (hur v a b c _ (A.2 v) τ hτ).2]
          simp
        · rcases (hS v).1 hv with hv | hv
          · rw [b1 v hv] at hx
            exact cupB_sub_cob _ (ρ.comp (Dec (F := F) (A.1 v)).subtype) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P
              (fun g x y => hP g.1 x y) x.1 _ _ m x.2.1 x.2.2
              ((hsub ρ' hc' _).comp (continuous_id.prodMk continuous_const)) (fun g => hm' g.1) (k3 v hv x hx)
          · obtain ⟨m', hm''⟩ := k2 v hv
            refine ((hloc v).1 (restrictCocycles1 ρ' _ continuous_subtype_val y)).2 ⟨m' - m, fun g => ?_⟩ x
            change y.1 g.1 = ρ' g.1 (m' - m) - (m' - m)
            rw [hm', hm'' g.1 g.2, map_sub]
            abel
      · rintro ⟨k1, k2⟩
        refine ⟨y, ⟨fun v a b c => k1 v ((hS' v).2 ⟨a, b, c⟩), fun v hv => ?_, fun v hv x hx => ?_⟩, rfl⟩
        · obtain ⟨m, hm⟩ := ((hloc v).1 (restrictCocycles1 ρ' _ continuous_subtype_val y)).1 fun x =>
            k2 v ((hS v).2 (.inr hv)) x (by rw [b2 v hv]; trivial)
          exact ⟨m, fun g hg => hm ⟨g, hg⟩⟩
        · exact k2 v ((hS v).2 (.inl hv)) x (by rw [b1 v hv]; exact hx))
  refine ⟨fC, ?_⟩
  have hd : Disjoint hfin.toFinset (hT.toFinset ∪ Q) := Finset.disjoint_right.2 fun v hv h =>
    hnl v (by simpa using hv) (by simpa using h)
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin] at hcount
  have e1 : ∏ v ∈ hfin.toFinset, Nat.card (bkCond ρ A l (T ∪ ↑Q) L v) = ∏ v ∈ hfin.toFinset, Nat.card (L v) :=
    Finset.prod_congr rfl fun v hv => by rw [b1 v (by simpa using hv)]
  have e2 : ∏ v ∈ hT.toFinset ∪ Q, Nat.card (bkCond ρ A l (T ∪ ↑Q) L v) =
      (∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
        ∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ∈ T ∨ v ∈ Q := by simpa using hv
    rw [b2 v hv', Nat.card_congr Submodule.topEquiv.toEquiv]
    exact (hloc v).2 (hnl v hv')
  have e3 : ∏ v ∈ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) =
      ∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) :=
    Finset.prod_subset Finset.subset_union_right fun v hv hv' => by
      have : v ∈ T ∨ v ∈ Q := by simpa using hv
      rw [hT0 v (this.resolve_right hv')]
      exact Nat.card_unique
  have hpos : 0 < (∏ v ∈ hfin.toFinset ∪ (hT.toFinset ∪ Q), Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
      Nat.card W ^ InfinitePlace.nrComplexPlaces F :=
    mul_pos (Finset.prod_pos fun v _ => Nat.card_pos) (pow_pos Nat.card_pos _)
  rw [h0, h0', Nat.card_unique (α := (⊥ : Submodule Λ W)), Nat.card_unique (α := (⊥ : Submodule Λ W')), mul_one, mul_one,
    Finset.prod_union hd (f := fun v => Nat.card (bkCond ρ A l (T ∪ ↑Q) L v)), e1, e2, hcount, ← e3, mul_assoc] at e
  refine Nat.eq_of_mul_eq_mul_right hpos (e.trans ?_)
  rw [Finset.prod_union hd]
  ring

end General

theorem orderFormula : PoitouTateTotallyComplex → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q := by
  intro hPT hLF hLD hLE hGF hGE h4 D N X bkP i s A _ _ _ _ κ Q ρ hS hK hD hNI Y Y' _ _ _ _ _ _ _ _ _ _ β hβ
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := hS.2.1
  have hcx : InfinitePlace.nrComplexPlaces D.host.E = D.R.f := by
    have h1 := IsTotallyComplex.finrank D.host.E
    have h2 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
      rw [D.host.finrank_cmField]
      unfold Ranks.f Ranks.n
      ring
    omega
  obtain ⟨hc, hc', hP, hU⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y Y' β hβ.1
  have hcount := GlobalTheory.T.localConditionOrder_aboveL_finiteModules D N X bkP i s A κ Q hS hK
    (GlobalTheory.LocalSaturation.main hLF hLD hLE h4 D N X bkP i s A κ Q hS)
    (GlobalTheory.LocalConditionCount.locCount hLF hLD hLE h4 D N X bkP i s A κ Q hS) Y
  have hko : IsOpen ((κ⁻¹).ker : Set (GE N)) := by
    convert hS.2.2.2.1 using 2
    ext g
    simp
  refine order_formula (X.l i) (nu X i + 1) hPT hLF hLD hLE hGF hGE (repOn (Tgl i s) κ Y) (repOn ρ κ⁻¹ Y') (vecPair D.R.r β)
    (show 0 < nu X i + 1 by omega) hc hc' (fun x hx => funext fun c => hβ.2.1 _ fun y' => ?_) (fun y hy => funext fun c => hβ.2.2 _ fun x => ?_) hP
    N.plOm (Spl i) (GlobalTheory.SelObstruction.finite_Spl i) Q (fun v hv => hv.2) hS.2.2.2.2.2.2.1 hU
    (bkOn bkP i (Tgl i s) κ Y) (DualCl bkP i s κ ρ β Q) (fun c => Iff.rfl)
    (GlobalTheory.NoGlobalInv.noInv D N X bkP i s A κ Q hS Y (tors_all A Y)) (eq_bot_iff.2 fun m hm => hNI Y' m hm)
    (fun v hv => (GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s hS.1 v hv A κ⁻¹ hko (fun g => ?_) Y'
      (tors_all A Y') ρ (.inr hD)).1) ?_
  · have := hx (Pi.single c y')
    rw [vecPair_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  · have := hy (Pi.single c x)
    rw [vecPair_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  · obtain ⟨n, hn⟩ := hS.2.2.2.2.1 g
    exact ⟨n, by rw [MonoidHom.inv_apply, inv_pow, hn, inv_one]⟩
  · rw [hcount, hcx, Nat.card_pi, Finset.prod_const, Finset.card_fin, ← pow_mul, mul_comm D.R.r]

end GlobalTheory.SelOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearProjectiveModuleComposeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_projective_module_compose : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h → ∀ (A : Type) [CommRing A] (k : A →+* B.A) (N : Type) [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] [Module.Finite B.A N'] [Module.Projective B.A N'] (N'' : Type) [AddCommGroup N''] [Module C.A N''] (u : N →ₛₗ[k] N') (v : N' →ₛₗ[h.f] N'') (w : N →ₛₗ[h.f.comp k] N''), (∀ x, w x = v (u x)) → SemiBC v → SemiBC w → SemiBC u := by
  first | exact @GlobalTheory.BSP.semiBC_of_cover | exact GlobalTheory.BSP.semiBC_of_cover | (intros; apply GlobalTheory.BSP.semiBC_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenFiniteOfNoTower
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.PMon.Ram

theorem senFinite_of_noTower (hNT : NoTower) : SenFinite := by
  intro l _ n _ _ K ρ hc M hM
  obtain ⟨N, hN, hanti, hopen, hpow, hroot, hker⟩ := GlobalTheory.T.exists_congruenceFiltration_galoisRep l n K ρ hc
  have hdet := GlobalTheory.T.exists_detecting_characters_congr_filtration l n K ρ M hM N hN
  obtain ⟨k, hk⟩ := hNT l K N hanti hopen hpow hroot hdet
  refine GlobalTheory.T.finite_image_of_trivial_on_inf_isOpen l K (GL n ℚ_[l]) ρ (IK K) (N k) (hopen k) ?_
  intro g hgI hgN
  exact hker g (fun j => hk j ⟨hgI, hgN⟩)

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultisetBaseLatticeEqJumpsModStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senMultiset_base_lattice_eq_jumps_mod : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ i x, sen ((F.D A).γ i) (N i) x = resCount (U i) 0 x := by
  first | exact @GlobalTheory.BaseSen.sen_base | exact GlobalTheory.BaseSen.sen_base | (intros; apply GlobalTheory.BaseSen.sen_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallIdealNeBot
section
namespace GlobalTheory.SmallPrimeIdeal

open NumberField

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {y : K}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  obtain ⟨p, hp, hpy⟩ := hy
  by_contra hlt
  rw [not_le] at hlt

  have heq : y ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i = 0 := by
    rw [hp.as_sum] at hpy
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow] at hpy
    simp only [algebraMap_int_eq, eq_intCast] at hpy
    exact hpy
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at heq
    simp at heq
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hpos.ne') (fun i => (p.coeff i : K) * y ^ i)
  have hnorm : ‖y‖ ^ p.natDegree = ‖∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i‖ := by
    rw [← norm_pow, eq_neg_of_add_eq_zero_left heq, norm_neg]
  have hterm : ‖(p.coeff i : K) * y ^ i‖ < ‖y‖ ^ p.natDegree := by
    rw [norm_mul, norm_pow]
    calc ‖(p.coeff i : K)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ i :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K _) (by positivity)
      _ = ‖y‖ ^ i := one_mul _
      _ < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  linarith

theorem norm_int_le_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : ‖a (x : L)‖ ≤ 1 := by

  exact norm_le_one_of_isIntegral ((NumberField.RingOfIntegers.isIntegral_coe x).map a.toIntAlgHom)

def smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : Ideal (𝓞 L) where
  carrier := {x | ‖a (x : L)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have h : ‖a (x : L) + a (y : L)‖ ≤ max ‖a (x : L)‖ ‖a (y : L)‖ :=
      IsUltrametricDist.norm_add_le_max _ _
    have e : a ((x + y : 𝓞 L) : L) = a (x : L) + a (y : L) := by simp
    change ‖a ((x + y : 𝓞 L) : L)‖ < 1
    rw [e]
    exact lt_of_le_of_lt h (max_lt hx hy)
  smul_mem' := by
    intro c x hx
    have e : a ((c • x : 𝓞 L) : L) = a (c : L) * a (x : L) := by simp
    change ‖a ((c • x : 𝓞 L) : L)‖ < 1
    rw [e, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le_one a c) (norm_nonneg _) hx

theorem mem_smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : x ∈ smallIdeal a ↔ ‖a (x : L)‖ < 1 := by
  exact Iff.rfl

theorem norm_eq_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) (h : ¬ ‖a (x : L)‖ < 1) : ‖a (x : L)‖ = 1 := by
  exact le_antisymm (norm_int_le_one a x) (not_lt.mp h)

theorem smallIdeal_isPrime {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : (smallIdeal a).IsPrime := by
  refine ⟨?_, ?_⟩
  ·
    rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro x y hxy
    rw [mem_smallIdeal] at hxy
    rw [mem_smallIdeal, mem_smallIdeal]
    by_contra hc
    push Not at hc
    obtain ⟨hx, hy⟩ := hc
    have e : a ((x * y : 𝓞 L) : L) = a (x : L) * a (y : L) := by simp
    rw [e, norm_mul, norm_eq_one a x (not_lt.mpr hx), norm_eq_one a y (not_lt.mpr hy)] at hxy
    norm_num at hxy

theorem exists_local_dvd {L : Type} [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P ≠ ⊥) (u v : 𝓞 L) :
    ∃ r s : 𝓞 L, s ∉ P ∧ (u * r = v * s ∨ v * r = u * s) := by

  let Rp := Localization.AtPrime P
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP Rp
  have hinj : Function.Injective (algebraMap (𝓞 L) Rp) :=
    IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors
  rcases ValuationRing.dvd_total (algebraMap (𝓞 L) Rp u) (algebraMap (𝓞 L) Rp v) with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inl (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inr (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]

theorem smallIdeal_ne_bot {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a : L →+* PadicAlgCl l) : smallIdeal a ≠ ⊥ := by

  intro hbot
  have hl : ((l : 𝓞 L)) ∈ smallIdeal a := by
    rw [mem_smallIdeal]
    have e : a ((l : 𝓞 L) : L) = (l : PadicAlgCl l) := by simp
    have hext := PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])
    rw [map_natCast] at hext
    rw [e, hext, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [hbot, Ideal.mem_bot] at hl
  have h0 : ((l : 𝓞 L) : L) = 0 := by rw [hl]; simp
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h0)

theorem le_one_of_le_one {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a b : L →+* PadicAlgCl l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < 1 ↔ ‖b (x : L)‖ < 1) (x : L) (hx : ‖a x‖ ≤ 1) :
    ‖b x‖ ≤ 1 := by
  classical
  have hb : ∀ y : 𝓞 L, y ∈ smallIdeal a ↔ ‖b (y : L)‖ < 1 := fun y => (mem_smallIdeal a y).trans (h y)
  have := smallIdeal_isPrime a

  obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (𝓞 L) x
  change ‖a ((u : L) / (w : L))‖ ≤ 1 at hx
  change ‖b ((u : L) / (w : L))‖ ≤ 1
  have hw0 : (w : L) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hw
    exact_mod_cast this

  obtain ⟨r, s, hs, hrs⟩ := exists_local_dvd (smallIdeal a) (smallIdeal_ne_bot a) u w
  have hs0 : (s : L) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact (smallIdeal a).zero_mem
  have hbs : ‖b (s : L)‖ = 1 := norm_eq_one b s (fun hlt => hs ((hb s).mpr hlt))
  have has : ‖a (s : L)‖ = 1 := norm_eq_one a s (fun hlt => hs ((mem_smallIdeal a s).mpr hlt))
  rcases hrs with h1 | h1
  ·
    have h1' : (u : L) * r = w * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have hr0 : (r : L) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1'
      exact mul_ne_zero hw0 hs0 h1'.symm
    have e : (u : L) / w = s / r := by
      rw [div_eq_div_iff hw0 hr0]
      linear_combination h1'
    rw [e] at hx ⊢
    rw [map_div₀, norm_div, has] at hx
    have hpos : 0 < ‖a (r : L)‖ := norm_pos_iff.mpr ((map_ne_zero a).mpr hr0)
    have har : ¬ ‖a (r : L)‖ < 1 := by
      intro hlt
      rw [div_le_iff₀ hpos] at hx
      linarith
    have hbr : ‖b (r : L)‖ = 1 := norm_eq_one b r (fun hlt => har ((h r).mpr hlt))
    rw [map_div₀, norm_div, hbs, hbr, div_one]
  ·
    have h1' : (w : L) * r = u * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have e : (u : L) / w = r / s := by
      rw [div_eq_div_iff hw0 hs0]
      linear_combination -h1'
    rw [e, map_div₀, norm_div, hbs, div_one]
    exact norm_int_le_one b r

theorem norm_le_one_iff {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact (Nat.Prime l)]
    (a b : L →+* Formalism.ConjugateSelfDual.Qbar l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < (1 : ℝ) ↔ ‖b (x : L)‖ < (1 : ℝ)) (x : L) :
    ‖a x‖ ≤ (1 : ℝ) ↔ ‖b x‖ ≤ (1 : ℝ) := by
  exact ⟨le_one_of_le_one a b h x, le_one_of_le_one b a (fun y => (h y).symm) x⟩

end GlobalTheory.SmallPrimeIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameRelationCocycleSquareZeroInertiaStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_relation_cocycle_squareZero_inertia : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ (k : ℕ), normV v % (2 * l ^ k) = 1 → ∀ (M : ℕ) (d : G F Ω →* Multiplicative (ZMod (l ^ M))) (γ σ : G F Ω), 1 ≤ M → IsOpen (d.ker : Set (G F Ω)) → γ ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) σ → ∀ (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R (G F Ω) W) (a b : R), (∀ m : W, (l ^ k) • m = 0) → b * b = 0 → (∀ τ ∈ Ine (F := F) A, ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m) → (∀ m, ρ σ m = m + a • m) → ∀ z : Z1 ρ, a • z.1 γ = b • z.1 σ ∧ (b = 0 → z.1 γ = 0 → ∀ τ ∈ Ine (F := F) A, z.1 τ = 0) := by
  first | exact @GlobalTheory.TameRelation.tame_relation | exact GlobalTheory.TameRelation.tame_relation | (intros; apply GlobalTheory.TameRelation.tame_relation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaGaloisFixedOfCongrBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_galois_fixed_of_congr_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Per.BdRp l) (M k : ℕ) (s : bk.S), (l : Per.BdRp l) ^ k * aDp l (bk.ev bk.E) ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l (M + 1) → ∀ g : ↥(GK K), Per.σC (g : GQ l) (Per.θD l x) = Per.θD l x := by
  first | exact @GlobalTheory.BKLim.theta_gal_fixed_of_congr | exact GlobalTheory.BKLim.theta_gal_fixed_of_congr | (intros; apply GlobalTheory.BKLim.theta_gal_fixed_of_congr <;> assumption)
end

