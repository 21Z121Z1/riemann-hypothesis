import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CmHostIdempotentTraceEqOne
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.QuadTrace

theorem bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by
  have hd : 0 < H.d := H.d_prime.pos
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have e := H.bar_eq H.rt
    rw [h] at e
    have e2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← IsCMField.complexEmbedding_complexConj, ← e]
    have e3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
      simpa using this
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
    rw [hr] at e3
    have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
    have : (0 : ℝ) < H.d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]
  · exact h

theorem cmHost_idempotent_trace_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.HostTraceIdentity H := by
  intro E _ _ _ H _ hstar
  rw [hstar]
  have hb := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, bar_rt, map_ofNat] at hb
  have h2 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    linear_combination H.two_weight_eq_one_add_root + hb
  exact mul_left_cancel₀ two_ne_zero h2

end GlobalTheory.QuadTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesOfNaturalNilpotentPoints
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

section
variable {R : Type} [CommRing R] (I : Ideal R) (n d : ℕ)

private abbrev MainNotions (k : ℕ) : Type :=
  Geo.Tor.JetR R (Fin n × Fin d) k ⧸ (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) k))

private def xK (k : ℕ) : Fin n → Fin d → MainNotions I n d k := fun i j =>
  Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (MvPolynomial.X (i, j)))

private abbrev JJ : Ideal (PS R n d) :=
  I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n × Fin d) R) ⊔
    Ideal.span (Set.range (MvPowerSeries.X : Fin n × Fin d → MvPowerSeries (Fin n × Fin d) R))

variable {n d}

private def Lev (k : ℕ) (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S) : Prop :=
  Kills I k S ∧ Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2) ^ (k + 1) = ⊥

variable {I}

private theorem Lev.mono {k k' : ℕ} (h : k ≤ k') {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) : Lev I k' S a :=
  ⟨fun t ht => ha.1 t (Ideal.pow_le_pow_right (by omega) ht),
    le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans ha.2.le)⟩

private theorem Lev.nil {k : ℕ} {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) (i : Fin n) (j : Fin d) : IsNilpotent (a i j) := by
  refine ⟨k + 1, ?_⟩
  rw [← Ideal.mem_bot, ← ha.2]
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self (f := fun q : Fin n × Fin d => a q.1 q.2) (i, j))) _

private theorem exists_lev {S : Type} [CommRing S] [Algebra R S] {a : Fin n → Fin d → S}
    (hk : ∃ k, Kills I k S) (ha : ∀ i j, IsNilpotent (a i j)) : ∃ k, Lev I k S a := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (I := Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2)) (J := ⊥)
    (Ideal.span_le.2 (by rintro _ ⟨q, rfl⟩; exact ha q.1 q.2))
    (Submodule.fg_span (Set.finite_range _))
  exact ⟨k + m, fun t ht => hk t (Ideal.pow_le_pow_right (by omega) ht),
    le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans hm)⟩

private theorem exists_lift {k : ℕ} {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) :
    ∃ φ : MainNotions I n d k →ₐ[R] S, ∀ i j, φ (xK I n d k i j) = a i j := by
  let φ₀ : Geo.Tor.JetR R (Fin n × Fin d) k →ₐ[R] S :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun q : Fin n × Fin d => a q.1 q.2)
      (aeval_kill k _ _ (fun q => Ideal.subset_span (Set.mem_range_self q)) ha.2)
  refine ⟨Ideal.Quotient.liftₐ _ φ₀ fun y hy => ?_, fun i j => ?_⟩
  · have : (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) k)) ≤
        RingHom.ker φ₀.toRingHom := by
      refine Ideal.map_le_iff_le_comap.2 fun t ht => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact (φ₀.commutes t).trans (ha.1 t ht)
    exact this hy
  · exact MvPolynomial.aeval_X (fun q : Fin n × Fin d => a q.1 q.2) (i, j)

private theorem lev_xK (k : ℕ) : Lev I k (MainNotions I n d k) (xK I n d k) := by
  refine ⟨fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ht), ?_⟩
  have h := congrArg (Ideal.map (Ideal.Quotient.mk
    ((I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) k)))))
    (jet_aug_pow (T := R) (Fin n × Fin d) k)
  rw [Ideal.map_pow _ (Ideal.map _ (Ideal.span _)), Ideal.map_bot, Ideal.map_span, Ideal.map_span, ← Set.range_comp,
    ← Set.range_comp] at h
  exact h

private theorem hom_coe {S : Type} [CommRing S] [Algebra R S] (ψ : PS R n d →+* S)
    (hC : ∀ c, ψ (MvPowerSeries.C c) = algebraMap R S c) (p : MvPolynomial (Fin n × Fin d) R) :
    ψ (p : MvPowerSeries (Fin n × Fin d) R) =
      MvPolynomial.aeval (fun q => ψ (MvPowerSeries.X q)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.coe_C, MvPolynomial.aeval_C]; exact hC c
  | add p q hp hq => rw [MvPolynomial.coe_add, map_add, map_add, hp, hq]
  | mul_X p q hp => rw [MvPolynomial.coe_mul, map_mul, map_mul, hp, MvPolynomial.coe_X, MvPolynomial.aeval_X]

private theorem hom_kill {k : ℕ} {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) (ψ : PS R n d →+* S)
    (hC : ∀ c, ψ (MvPowerSeries.C c) = algebraMap R S c)
    (hX : ∀ q : Fin n × Fin d, ψ (MvPowerSeries.X q) = a q.1 q.2) (g : PS R n d)
    (hg : g ∈ JJ I n d ^ (k + 1 + (k + 1))) : ψ g = 0 := by
  have h1 : JJ I n d ^ (k + 1 + (k + 1)) ≤ RingHom.ker ψ := by
    refine Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le ?_ ?_)
    · rw [← Ideal.map_pow]
      refine Ideal.map_le_iff_le_comap.2 fun t ht => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact (hC t).trans (ha.1 t ht)
    · rw [RingHom.ker, ← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, ← Set.range_comp,
        ← ha.2]
      exact le_of_eq (by congr 3; exact funext hX)
  exact h1 hg

private theorem exists_poly (N : ℕ) (g : PS R n d) :
    ∃ p : MvPolynomial (Fin n × Fin d) R, g - (p : MvPowerSeries (Fin n × Fin d) R) ∈ JJ I n d ^ N := by
  refine ⟨MvPowerSeries.truncTotal N g,
    ((mem_sup_span_X_pow_iff_and_isAdicComplete R I (Fin n × Fin d)).1 N _).2 fun e => ?_⟩
  by_cases he : e.degree < N
  · rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ he, sub_self]
    exact Ideal.zero_mem _
  · rw [show N - e.degree = 0 by omega]
    simp

private theorem nv_lift {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (φ : S →ₐ[R] S') {a : Fin n → Fin d → S} (ha : ∀ i j, IsNilpotent (a i j)) (g : PS R n d) :
    φ (nv (algebraMap R S) g a) = nv (algebraMap R S') g (fun i j => φ (a i j)) := by
  have h := (nv_calculus R S (algebraMap R S) n d a ha).2.2.2.2.1 S' φ.toRingHom g
  rw [show φ.toRingHom.comp (algebraMap R S) = algebraMap R S' from RingHom.ext φ.commutes] at h
  exact h

private theorem mem_of_nv_eq (k : ℕ) (g g' : PS R n d)
    (h : nv (algebraMap R _) g (xK I n d k) = nv (algebraMap R _) g' (xK I n d k)) :
    g - g' ∈ JJ I n d ^ (k + 1) := by
  let π : PS R n d →+* PS R n d ⧸ JJ I n d ^ (k + 1) := Ideal.Quotient.mk _
  have hπC : ∀ c, π (MvPowerSeries.C c) = algebraMap R _ c := fun c => rfl
  have hl : Lev I k (PS R n d ⧸ JJ I n d ^ (k + 1)) (fun i j => π (MvPowerSeries.X (i, j))) := by
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [← hπC]
      refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_right_mono le_sup_left _ ?_)
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ht
    · rw [← le_bot_iff, ← Ideal.map_quotient_self (JJ I n d ^ (k + 1)), Ideal.map_pow]
      refine Ideal.pow_right_mono (Ideal.span_le.2 ?_) _
      rintro _ ⟨q, rfl⟩
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩))
  obtain ⟨φ, hφ⟩ := exists_lift hl
  obtain ⟨ψ, hψ, hC, hX⟩ := (nv_calculus R _ (algebraMap R _) n d _ hl.nil).1
  have hψπ : ∀ u, ψ u = π u := fun u => by
    obtain ⟨p, hp⟩ := exists_poly (I := I) (k + 1 + (k + 1)) u
    have h1 := hom_kill hl ψ hC hX _ hp
    have h2 := hom_kill hl π hπC (fun _ => rfl) _ hp
    rw [map_sub, sub_eq_zero] at h1 h2
    rw [h1, h2, hom_coe ψ hC, hom_coe π hπC]
    simp only [hX]
  have h3 := congrArg φ h
  rw [nv_lift φ (lev_xK k).nil, nv_lift φ (lev_xK k).nil] at h3
  simp only [hφ] at h3
  rw [← hψ, ← hψ, hψπ, hψπ] at h3
  exact Ideal.Quotient.eq.1 h3

private theorem nv_surj (k : ℕ) (y : MainNotions I n d k) :
    ∃ g : PS R n d, nv (algebraMap R _) g (xK I n d k) = y := by
  obtain ⟨ψ, hψ, hC, hX⟩ := (nv_calculus R _ (algebraMap R _) n d _ (lev_xK (I := I) k).nil).1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨(p : MvPowerSeries (Fin n × Fin d) R), ?_⟩
  rw [← hψ, hom_coe ψ hC]
  have : MvPolynomial.aeval (fun q => ψ (MvPowerSeries.X q)) =
      (Ideal.Quotient.mkₐ R _).comp (Ideal.Quotient.mkₐ R _) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [MvPolynomial.aeval_X, hX]
    rfl
  rw [this]
  rfl

private theorem const_add_nil (k : ℕ) (y : MainNotions I n d k) :
    ∃ r : R, IsNilpotent (y - algebraMap R _ r) := by
  obtain ⟨g, rfl⟩ := nv_surj k y
  obtain ⟨⟨ψ, hψ, hC, -⟩, h0, -⟩ := nv_calculus R _ (algebraMap R _) n d _ (lev_xK (I := I) k).nil
  refine ⟨MvPowerSeries.constantCoeff g, ?_⟩
  have := (h0 (g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)) (by simp)).1
  rwa [← hψ, map_sub, hC, hψ] at this

end

theorem exists_series_of_natural : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (n d : ℕ) (L : ∀ (S : Type) [CommRing S] [Algebra R S], Prop), (∀ (k m : ℕ), L (Geo.Tor.JetR R (Fin n × Fin d) m ⧸ (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) m)))) → ∀ (c : ∀ (S : Type) [CommRing S] [Algebra R S], (Fin n → Fin d → S) → S), (∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (a : Fin n → Fin d → S), L S → L S' → (∀ y : S, ∃ r : R, IsNilpotent (y - algebraMap R S r)) → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → φ (c S a) = c S' (fun i j => φ (a i j))) → ∃ f : PS R n d, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), L S → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S a = nv (algebraMap R S) f a := by
  intro R _ I hI n d L hL c hc
  choose g hg using fun k => nv_surj k (c (MainNotions I n d k) (xK I n d k))
  have key : ∀ (k : ℕ) (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), L S →
      Lev I k S a → c S a = nv (algebraMap R S) (g k) a := by
    intro k S _ _ a hS ha
    obtain ⟨φ, hφ⟩ := exists_lift ha
    have h1 := hc _ S φ (xK I n d k) (hL k k) hS (const_add_nil k) ⟨k, (lev_xK k).1⟩ (lev_xK k).nil
    rw [← hg, nv_lift φ (lev_xK k).nil] at h1
    simp only [hφ] at h1
    exact h1.symm
  have hcomp : IsAdicComplete (JJ I n d) (PS R n d) :=
    (mem_sup_span_X_pow_iff_and_isAdicComplete R I (Fin n × Fin d)).2 hI
  obtain ⟨f, hf⟩ := hcomp.toIsPrecomplete.prec (f := g) fun {k k'} h => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    refine Ideal.pow_le_pow_right (Nat.le_succ k) (mem_of_nv_eq k _ _ ?_)
    rw [← key k _ _ (hL k k) (lev_xK k), ← key k' _ _ (hL k k) ((lev_xK k).mono h)]
  refine ⟨f, fun S _ _ a hS hk ha => ?_⟩
  obtain ⟨k, hk⟩ := exists_lev hk ha
  obtain ⟨ψ, hψ, hC, hX⟩ := (nv_calculus R _ (algebraMap R S) n d _ ha).1
  have h1 := hf (k + 1 + (k + 1))
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hom_kill hk ψ hC hX _ h1
  rw [map_sub, sub_eq_zero, hψ, hψ] at h2
  rw [key (k + 1 + (k + 1)) S a hS (hk.mono (by omega)), h2]

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentChartsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_reading_groupHom_nilpotentCharts : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'] (d e : ℕ) (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (X : Fam G d) (X' : Fam G' e), NilChart G F X → NilChart G' F' X' → ∀ f : G ⟶ G', IsMonHom f → ∃ φ : Fin e → PS R 1 d, Reads X X' f φ := by
  first | exact @GlobalTheory.ChF.exists_reads | exact GlobalTheory.ChF.exists_reads | (intros; apply GlobalTheory.ChF.exists_reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHomStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupAction_linearPart_ringHom : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (OE : Type) [CommRing OE] (act : Geo.Tor.Germ.OAct OE F) (S : Type) [CommRing S] (β : R →+* S), ∃ ρ : OE →+* Matrix (Fin d) (Fin d) S, ∀ a, ρ a = linPart (actMap β act a) ∧ ρ a = (lin (act.act a)).map β := by
  first | exact @GlobalTheory.ChF.linPart_act_ringHom | exact GlobalTheory.ChF.linPart_act_ringHom | (intros; apply GlobalTheory.ChF.linPart_act_ringHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawJacobianExtensionChangeCoeffStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLaw_jacobian_extension_changeCoeff : ∀ (R S : Type) [CommRing R] [CommRing S] (β : R →+* S), (∀ (d : ℕ) (F : FGLaw R d), ∃ F' : FGLaw S d, F'.F = F.mapF β) ∧ (∀ (d e : ℕ) (φ : Fin e → PS R 1 d), lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β) ∧ ∀ (d g r : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q → ExtSer (F.mapF β) (FB.mapF β) (fun j => MvPowerSeries.map β (J j)) (fun j => MvPowerSeries.map β (Q j)) := by
  first | exact @GlobalTheory.ChF.changeCoeff_law_lin_extSer | exact GlobalTheory.ChF.changeCoeff_law_lin_extSer | (intros; apply GlobalTheory.ChF.changeCoeff_law_lin_extSer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalSeriesJacobianChainRuleLinearPart
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hs {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (h : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => h q.1 q.2)

private theorem sub_sub' {R : Type} [CommRing R] {m n k d e f : ℕ} (a : Fin m → Fin d → PS R n e)
    (b : Fin n → Fin e → PS R k f) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) (u : PS R m d) :
    sub b (sub a u) = sub (fun i j => sub b (a i j)) u :=
  MvPowerSeries.subst_comp_subst_apply (hs a ha) (hs b hb) u

private theorem sub_X {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (q : Fin m × Fin d) :
    sub a (MvPowerSeries.X q) = a q.1 q.2 :=
  MvPowerSeries.subst_X (hs a ha) q

private theorem sub_mul' {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u v : PS R m d) :
    sub a (u * v) = sub a u * sub a v :=
  MvPowerSeries.subst_mul (hs a ha) u v

private theorem const_sub {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u : PS R m d) :
    MvPowerSeries.constantCoeff (sub a u) = MvPowerSeries.constantCoeff u := by
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R R (RingHom.id R) n e 0 (fun _ _ => IsNilpotent.zero)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R R (RingHom.id R) m d 0 (fun _ _ => IsNilpotent.zero)
  have h6 := h6 (by simp)
  have h6' := h6' (by simp)
  have h := h3 m d a u ha
  have e0 : (fun i j => nv (RingHom.id R) (a i j) 0) = 0 := by
    funext i j
    rw [h6, ha]; simp
  rw [e0, h6, h6'] at h
  simpa using h

private theorem coeff_sub {R : Type} [CommRing R] {d e : ℕ} (φ : Fin e → PS R 1 d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (u : PS R 1 e) (k : Fin d) :
    dl (sub ![φ] u) k = ∑ i, lin φ i k * dl u i := by
  classical
  have hφ' : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j; fin_cases i; exact hφ j
  let s : R →+* TrivSqZeroExt R R := algebraMap R _
  let a : Fin 1 → Fin d → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (if j = k then 1 else 0)
  let b : Fin 1 → Fin e → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (lin φ j k)
  have hn : ∀ x : R, IsNilpotent (TrivSqZeroExt.inr x : TrivSqZeroExt R R) := fun x =>
    ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R _ s 1 d a (fun _ _ => hn _)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R _ s 1 e b (fun _ _ => hn _)
  have h6 := h6 (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h6' := h6' (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h := h3 1 e ![φ] u hφ'
  have e0 : (fun i j => nv s ((![φ] : Fin 1 → _) i j) a) = b := by
    funext i j
    fin_cases i
    rw [h6, hφ']
    ext
    · have hf : ∀ (t : Finset (Fin 1 × Fin d)) (g : Fin 1 × Fin d → TrivSqZeroExt R R),
          (∑ q ∈ t, g q).fst = ∑ q ∈ t, (g q).fst := fun t g =>
        map_sum (TrivSqZeroExt.fstHom R R R) g t
      simp [s, a, b, hf, apply_ite TrivSqZeroExt.fst]
    · simp [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, lin, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e0, h6, h6'] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simpa [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, TrivSqZeroExt.algebraMap_eq_inl, dl,
    mul_comm] using h2

theorem chain_rule_lin : ∀ (R : Type) [CommRing R] (d e : ℕ) (φ : Fin e → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∀ u : PS R 1 e, dl (sub ![φ] u) = (lin φ)ᵀ *ᵥ dl u ∧ MvPowerSeries.constantCoeff (sub ![φ] u) = MvPowerSeries.constantCoeff u) ∧ (∀ (m : ℕ) (ψ : Fin m → PS R 1 e), lin (fun j => sub ![φ] (ψ j)) = lin ψ * lin φ) ∧ ∀ (F : FGLaw R d) (F' : FGLaw R e), IsHomF F.F F'.F φ → ∀ u, IsCh F'.F u → IsCh F.F (sub ![φ] u) := by
  intro R _ d e φ hφ
  have one : ∀ {n f g : ℕ} (x : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![x] : Fin 1 → _) i j) = 0 := by
    intro n f g x hx i j; fin_cases i; exact hx j
  have two : ∀ {n f g : ℕ} (x y : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      (∀ j, MvPowerSeries.constantCoeff (y j) = 0) →
      ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → _) i j) = 0 := by
    intro n f g x y hx hy i j; fin_cases i
    · exact hx j
    · exact hy j
  have hφ' := one φ hφ
  refine ⟨fun u => ⟨?_, const_sub _ hφ' u⟩, fun m ψ => ?_, fun F F' hF u hu => ⟨?_, ?_⟩⟩
  · funext k
    rw [coeff_sub φ hφ u k]
    rfl
  · ext j k
    have := coeff_sub φ hφ (ψ j) k
    rw [Matrix.mul_apply]
    refine this.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)
  · rw [const_sub _ hφ' u, hu.1]
  · have hpt : ∀ (f : ℕ) (i : Fin 2) j, MvPowerSeries.constantCoeff (pt R (n := 2) f i j) = 0 :=
      fun f i j => MvPowerSeries.constantCoeff_X _
    have hid : ∀ (f : ℕ) (G : Fin f → PS R 2 f), addOf G (pt R (n := 2) f 0) (pt R (n := 2) f 1) = G := by
      intro f G
      funext i
      have : (fun p : Fin 2 × Fin f => (![pt R (n := 2) f 0, pt R (n := 2) f 1] : Fin 2 → _) p.1 p.2)
          = MvPowerSeries.X := by
        funext ⟨p, q⟩
        fin_cases p <;> rfl
      simp only [addOf, ev]
      rw [this, MvPowerSeries.subst_self]
      rfl
    have hu2 := hu.2
    rw [hid] at hu2 ⊢
    set x : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 0] (φ i) with hx
    set y : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 1] (φ i) with hy
    have hx0 : ∀ j, MvPowerSeries.constantCoeff (x j) = 0 := fun j => by
      rw [hx]; dsimp only; rw [const_sub _ (one _ (hpt d 0)), hφ]
    have hy0 : ∀ j, MvPowerSeries.constantCoeff (y j) = 0 := fun j => by
      rw [hy]; dsimp only; rw [const_sub _ (one _ (hpt d 1)), hφ]
    have hxy := two x y hx0 hy0
    have h : sub ![x, y] (sub ![F'.F] u) =
        sub ![x, y] (sub ![pt R (n := 2) e 0] u * sub ![pt R (n := 2) e 1] u) := congrArg _ hu2
    rw [sub_mul' _ hxy, sub_sub' _ _ (one _ F'.const) hxy, sub_sub' _ _ (one _ (hpt e 0)) hxy,
      sub_sub' _ _ (one _ (hpt e 1)) hxy] at h
    change sub ![F.F] (sub ![φ] u) =
      sub ![pt R (n := 2) d 0] (sub ![φ] u) * sub ![pt R (n := 2) d 1] (sub ![φ] u)
    rw [sub_sub' _ _ hφ' (one _ F.const), sub_sub' _ _ hφ' (one _ (hpt d 0)),
      sub_sub' _ _ hφ' (one _ (hpt d 1))]
    have e1 : (fun i j => sub ![F.F] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![F'.F] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact hF.2 j
    have e2 : (fun i j => sub ![pt R (n := 2) d 0] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 0] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (0, j)).symm
    have e3 : (fun i j => sub ![pt R (n := 2) d 1] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 1] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (1, j)).symm
    rw [e1, e2, e3]
    exact h

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSeriesEqOfEvalAtNilpotentPointsEqStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (n d : ℕ) (f f' : PS R n d), (∀ (S : Type) [CommRing S] [Algebra R S] (k : ℕ), Kills I k S → (IsLocalRing R → I ≠ ⊤ → IsLocalRing S ∧ IsLocalHom (algebraMap R S)) → ∀ a : Fin n → Fin d → S, (∀ i j, IsNilpotent (a i j)) → nv (algebraMap R S) f a = nv (algebraMap R S) f' a) → f = f' := by
  first | exact @GlobalTheory.ChF.eq_of_nv_eq | exact GlobalTheory.ChF.eq_of_nv_eq | (intros; apply GlobalTheory.ChF.eq_of_nv_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SeriesTwoPointsEqSumMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_mul_eval_two_points_of_free_finite_quotient : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (J : Ideal (PS O 1 d)), Module.Free O (PS O 1 d ⧸ J) → Module.Finite O (PS O 1 d ⧸ J) → ∀ f : PS O 2 d, ∃ (m : ℕ) (g h : Fin m → PS O 1 d), ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → (∀ u ∈ J, φ u = 0) → (∀ u ∈ J, φ' u = 0) → Φ f = ∑ i, φ (g i) * φ' (h i) := by
  first | exact @GlobalTheory.series_two_points_eq_sum_mul | exact GlobalTheory.series_two_points_eq_sum_mul | (intros; apply GlobalTheory.series_two_points_eq_sum_mul <;> assumption)
end

