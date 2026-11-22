import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsoluteGaloisMemFixingSubgroupMaxUnramified
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpace
section
open NumberField MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.StdLatSpan

variable (K : Type) [Field K] [NumberField K]

theorem toK_apply {σ : Type} (f : MvPolynomial σ (𝓞 K)) : toK K σ f = map (algebraMap (𝓞 K) K) f := rfl

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma nabStd_fg' (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : (_root_.Formalism.L2.DIV.nabStd K lam).FG := by
  classical
  unfold _root_.Formalism.L2.DIV.nabStd
  choose b hb _ using fun τ : ι => _root_.Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n (lam τ).natW
  have hinj : LinearMap.ker (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K))
  have hwb : ∀ τ, LinearIndependent (𝓞 K) (b τ) ∧
      Submodule.span (𝓞 K) (Set.range (b τ)) = _root_.Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n (lam τ).natW := by
    intro τ
    have h := hb τ
    unfold _root_.Formalism.GradedWeylDivisibility.IsWeightBasis at h
    exact ⟨h.1, h.2.1⟩
  haveI : ∀ τ, Finite ↑(_root_.Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := fun τ => (_root_.Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  obtain ⟨-, hspan⟩ := _root_.Formalism.GradedWeylDivisibility.tensorBasis (𝓞 K) K ι n n (fun τ => ↑(_root_.Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW))
    (fun τ => Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.nablaSq (𝓞 K) n (lam τ)))
    (fun τ i => _root_.Formalism.L2.DIV.toK K (Fin n × Fin n) (b τ i))
    (fun τ => (hwb τ).1.map' _ hinj)
    (fun τ => by
      rw [Set.range_comp' (g := _root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (f := b τ), ← Submodule.map_span, (hwb τ).2]
      rfl)
  rw [← hspan]
  exact Submodule.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma prod_image_blockEmb_eq_setOf_prod {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}
    (X : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    (∏ s ∈ Finset.univ, (_root_.Formalism.GradedWeylDivisibility.blockEmb K s : MvPolynomial (Fin k × Fin n) K → _) '' X s) =
      {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ X s) ∧
        P = ∏ s, _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s)} := by
  ext P
  rw [Set.mem_finset_prod]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose F hF hFe using fun s => hg (Finset.mem_univ s)
    exact ⟨F, hF, Finset.prod_congr rfl fun s _ => (hFe s).symm⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨fun s => _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s), fun {s} _ => ⟨F s, hF s, rfl⟩, rfl⟩

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_setOf_prod_blockEmb_eq_prod_map_span {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}
    (X : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    Submodule.span K {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ X s) ∧
        P = ∏ s, _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s)} =
      ∏ s, Submodule.map (_root_.Formalism.GradedWeylDivisibility.blockEmb K s).toLinearMap (Submodule.span K (X s)) := by
  rw [← prod_image_blockEmb_eq_setOf_prod, ← Submodule.prod_span]
  simp only [Submodule.map_span, AlgHom.coe_toLinearMap]

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_tensorLat_eq_prod_map_span {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S]
    {k n : ℕ} (L : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) :
    Submodule.span K (_root_.Formalism.GradedWeylDivisibility.tensorLat R K L : Set (MvPolynomial (S × Fin k × Fin n) K)) =
      ∏ s, Submodule.map (_root_.Formalism.GradedWeylDivisibility.blockEmb K s).toLinearMap (Submodule.span K (L s : Set _)) := by
  unfold _root_.Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_span_of_tower]
  exact span_setOf_prod_blockEmb_eq_prod_map_span (K := K) (k := k) (n := n)
    fun s => (L s : Set (MvPolynomial (Fin k × Fin n) K))

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_map_toK_nablaSq_eq_nablaSq (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : _root_.Formalism.BasicNotions.DomWeight n) :
    Submodule.span K (Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.nablaSq (𝓞 K) n μ) : Set _) =
      _root_.Formalism.BasicNotions.nablaSq K n μ := by
  unfold _root_.Formalism.BasicNotions.nablaSq
  obtain ⟨b, hb, -⟩ := _root_.Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n μ.natW
  rw [← _root_.Formalism.GradedWeylDivisibility.span_map_weightBasis_eq_dualWeyl (K := K) hb]
  have hspan : Submodule.span (𝓞 K) (Set.range b) = _root_.Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n μ.natW := by
    unfold _root_.Formalism.GradedWeylDivisibility.IsWeightBasis at hb
    exact hb.2.1
  rw [← hspan, Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  rfl

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_map_toK_delSq_eq_nablaSq (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : _root_.Formalism.BasicNotions.DomWeight n) :
    Submodule.span K (Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.delSq (𝓞 K) n μ) : Set _) =
      _root_.Formalism.BasicNotions.nablaSq K n μ := by
  rw [_root_.Formalism.L2.Col.nablaSq_eq_delSq]
  unfold _root_.Formalism.BasicNotions.delSq _root_.Formalism.GradedWeylDivisibility.weyl
  rw [Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  congr 2
  funext w
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [← _root_.Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, _root_.Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in

theorem _root_.GlobalTheory.StdLatSpan.std_fg_span : ∀ (K : Type) [Field K] [NumberField K] (ι : Type)
    [Fintype ι] (n : ℕ) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n),
    (_root_.Formalism.L2.DIV.nabStd K lam).FG ∧ (_root_.Formalism.L2.DIV.delStd K lam).FG ∧
      Submodule.span K (_root_.Formalism.L2.DIV.nabStd K lam : Set (_root_.Formalism.L2.DIV.Pol K ι n)) = _root_.Formalism.L2.DIV.VV K lam ∧
      Submodule.span K (_root_.Formalism.L2.DIV.delStd K lam : Set (_root_.Formalism.L2.DIV.Pol K ι n)) = _root_.Formalism.L2.DIV.VV K lam := by
  intro K _ _ ι _ n lam
  have hnab := nabStd_fg' K ι n lam
  refine ⟨hnab, hnab.of_le (_root_.Formalism.L2.DIV.delStd_le_nabStd K lam), ?_, ?_⟩
  · unfold _root_.Formalism.L2.DIV.nabStd _root_.Formalism.L2.DIV.VV
    rw [span_tensorLat_eq_prod_map_span, ← Submodule.span_eq (_root_.Formalism.GradedWeylDivisibility.tensorLat K K _), span_tensorLat_eq_prod_map_span]
    simp only [span_map_toK_nablaSq_eq_nablaSq, Submodule.span_eq]
  · unfold _root_.Formalism.L2.DIV.delStd _root_.Formalism.L2.DIV.VV
    rw [span_tensorLat_eq_prod_map_span, ← Submodule.span_eq (_root_.Formalism.GradedWeylDivisibility.tensorLat K K _), span_tensorLat_eq_prod_map_span]
    simp only [span_map_toK_delSq_eq_nablaSq, Submodule.span_eq]

end GlobalTheory.StdLatSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTheoremModule
section
noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Hyp

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime] (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem actVB_res (Y : Lat K LL) (g : ↥(GK K)) (g' : ↥(GK (levelField K s))) (hg : (g : GQ l) = g') :
    actVB ((LT l).PD K) Y.ρ g = actVB ((LT l).PD (levelField K s)) (resKs h Y) g' := by
  have h2 : Y.ρ g = resKs h Y g' := congrArg Y.ρ (Subtype.ext hg)
  have h3 : (((LT l).PD K).actB g).toAlgHom.toLinearMap.restrictScalars ℚ_[l] =
      (((LT l).PD (levelField K s)).actB g').toAlgHom.toLinearMap.restrictScalars ℚ_[l] :=
    LinearMap.ext fun b => (((LT l).PD_actB K g b).trans (by rw [hg])).trans
      ((LT l).PD_actB (levelField K s) g' b).symm
  unfold actVB
  rw [h2, h3]

theorem iInf_eq_of {α β γ : Type} [CompleteLattice γ] (f : α → γ) (g : β → γ)
    (h1 : ∀ a, ∃ b, f a = g b) (h2 : ∀ b, ∃ a, f a = g b) : ⨅ a, f a = ⨅ b, g b :=
  le_antisymm (le_iInf fun b => by obtain ⟨a, ha⟩ := h2 b; exact ha ▸ iInf_le f a)
    (le_iInf fun a => by obtain ⟨b, hb⟩ := h1 a; exact hb ▸ iInf_le g b)

theorem finrank_congr {R M : Type} [Field R] [AddCommGroup M] [Module R M] {X X' : Submodule R M}
    (e : X = X') : Module.finrank R ↥X = Module.finrank R ↥X' := by rw [e]

theorem fixed_eq (Y : Lat K LL) : (⨅ g : ((HW l).W K s LL h).GKs,
      LinearMap.ker (actVB ((LT l).PD K) Y.ρ (g : ↥(GK K)) - LinearMap.id)) =
      Dcris ((LT l).PD (levelField K s)) (resKs h Y) := by
  refine iInf_eq_of _ _ (fun g => ?_) fun g' => ?_
  · have hg : (g.1.1 : GQ l) ∈ GK (levelField K s) := (mem_GKs ((HW l).W_s K s LL h) g.1).mp g.2
    exact ⟨⟨g.1.1, hg⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y g.1 ⟨g.1.1, hg⟩ rfl)⟩
  · exact ⟨⟨⟨g'.1, GK_le (K := K) (K' := levelField K s) h.2.2.1 g'.2⟩,
      (mem_GKs ((HW l).W_s K s LL h) _).mpr g'.2⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y _ _ rfl)⟩

theorem crys_iff (Y : Lat K LL) :
    IsCrysOn (sit LT HW l AI K s LL h) (sit LT HW l AI K s LL h).W.GKs Y ↔
      IsCrys ((LT l).PD (levelField K s)) (resKs h Y) := by
  have h1 := finrank_congr (fixed_eq LT HW h Y)
  have h2 := congrArg (· * Module.finrank ↥LL.1 Y.V) (finrank_maxUnramified_levelFieldFiniteExtension K s h.1).symm
  exact iff_of_eq (congrArg₂ Eq h1 h2)

end Hyp

section Final

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

def lineLat {K LL : FinExt l} {ψ : ↥(GK K) →* (↥LL.1)ˣ} (L : Lattice (O := ↥(OL LL)) (charRep ψ))
    (hψ : Continuous fun g => ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) : Lat K LL where
  V := ↥LL.1
  modO := Algebra.toModule
  towO := inferInstance
  ρ := charRep ψ
  cont := fun _ => hψ.mul continuous_const
  L := L

variable (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

def TorsionBoundUnder {P : LocPrime l} {K LL : FinExt l} {s : ℕ} (h : Good K s LL)
    (Hyp : Lat K LL → ℕ → ℕ → Prop) (e : ℕ) : Prop :=
  ∀ (Y Yt : Lat K LL) (ι : LatHom Y.L Yt.L) (π : LatHom Yt.L (unitLat K LL)),
    IsSESLat (Qp := ℚ_[l]) ι π →
    IsCrys (P.PD (levelField K s)) (resKs h Yt) →
  ∀ M₀ h₀ : ℕ, Hyp Y M₀ h₀ →
  ∀ U : Finset ℤ, (∀ u, u ∈ U ↔ IsJump P h Y u) →
  ∀ x ∈ Yt.L.T, π.f x = 1 →
  ∀ c : ↥(GK K) → ↥Y.L.T, (∀ g, ι.f (c g : Y.V) = Yt.ρ g x - x) →
    PushInHf (P.PD K) (tateLat P K LL e) l (cTor K s (M₀ + h₀) U e) Y c

variable (D : Formalism.BasicNotions.D7) (H : HWOf D.loc) (F : FonOf D.loc D.locA H)

def TorsionTheoremModule : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (e : ℕ),
    TorsionBoundUnder (P := D.loc l) h
        (HypW (sit D.loc H l (D.locA l) K s LL h) ((F l).E K s LL h).tie) e ∧
      FiniteClasses (D.loc l) K LL e ∧ LengthBound (D.loc l) K LL e

end Final

end GlobalTheory.TorsionBoundCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSubOneMemSpanGaloisDifferences
section
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.KumIdeal

theorem exists_mul_modEq_ppow {p : ℕ} (hp : p.Prime) {n a : ℕ} (hn : 1 ≤ n) (ha : ¬ p ^ n ∣ a) :
    ∃ k, k * a ≡ p ^ (n - 1) [MOD p ^ n] := by
  have hd : Nat.gcd a (p ^ n) ∣ p ^ n := Nat.gcd_dvd_right _ _
  obtain ⟨v, hv, hv'⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hvn : v ≠ n := by
    intro h; apply ha; rw [← h, ← hv']; exact Nat.gcd_dvd_left _ _
  have hlt : Nat.gcd a (p ^ n) < p ^ n := by
    rw [hv']; exact Nat.pow_lt_pow_right hp.one_lt (lt_of_le_of_ne hv hvn)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hlt
  refine ⟨m * p ^ (n - 1 - v), ?_⟩
  have e : p ^ (n - 1) = p ^ v * p ^ (n - 1 - v) := by rw [← pow_add]; congr 1; omega
  rw [e, ← hv', ← hm]
  calc m * p ^ (n - 1 - v) * a = (a * m) * p ^ (n - 1 - v) := by ring
    _ ≡ (a * m % p ^ n) * p ^ (n - 1 - v) [MOD p ^ n] := (Nat.mod_modEq _ _).symm.mul_right _

theorem zeta_sub_one_mem_span : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt p r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ j : ℕ, 1 ≤ j → ∀ g ∈ Hinf T, g r ≠ r →
  T.ζ j - 1 ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x} := by
  intro p _ hp2 Ω _ _ hΩ T n r hr hK j hj g hg hgr
  classical
  have hp : p.Prime := Fact.out
  set C := FixI (Hfix T r) with hC
  set I := Submodule.span C {y : Ω | ∃ x ∈ C, y = g x - x} with hI
  have hr0 : r ≠ 0 := by rintro rfl; exact hgr (map_zero g)
  obtain ⟨y, E, hy, hE, huniq, hsum⟩ :=
    GlobalTheory.T.exists_integral_sum_conj_eq_zeta_sub_one p hp2 Ω hΩ T {r} (by simpa using hr) j hj
  have hE' : ∀ e ∈ E, e ∈ Hinf T := hE
  have huniq' : ∀ h ∈ Hinf T, ∃! e, e ∈ E ∧ h y = e y ∧ h r = e r := by
    intro h hh; simpa using huniq h hh
  have hex : ∀ k : Gal p Ω, ∃ e, k ∈ Hinf T → e ∈ E ∧ k y = e y ∧ k r = e r := by
    intro k
    by_cases hk : k ∈ Hinf T
    · obtain ⟨e, he, -⟩ := huniq' k hk; exact ⟨e, fun _ => he⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose rep hrep using hex
  have runiq : ∀ k ∈ Hinf T, ∀ e ∈ E, k y = e y → k r = e r → rep k = e := fun k hk e he h1 h2 =>
    (huniq' k hk).unique (hrep k hk) ⟨he, h1, h2⟩
  have hinv : ∀ h : Gal p Ω, ∀ x, h⁻¹ (h x) = x := fun h x => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hinv' : ∀ h : Gal p Ω, ∀ x, h (h⁻¹ x) = x := fun h x => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  let Y : Ω → Ω := fun ρ => ∑ e ∈ E with e r = ρ, e y
  have hYgal : ∀ h ∈ Hinf T, ∀ ρ, h (Y ρ) = Y (h ρ) := by
    intro h hh ρ
    simp only [Y, map_sum]
    have hmem : ∀ k ∈ Hinf T, ∀ e ∈ E, k * e ∈ Hinf T := fun k hk e he => mul_mem hk (hE' e he)
    refine Finset.sum_nbij' (fun e => rep (h * e)) (fun e => rep (h⁻¹ * e)) ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      obtain ⟨h1, -, h3⟩ := hrep _ (hmem h hh e he.1)
      exact ⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2]⟩
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      obtain ⟨h1, -, h3⟩ := hrep _ (hmem _ (inv_mem hh) e he.1)
      exact ⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2, hinv]⟩
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨h1, h2, h3⟩ := hrep _ (hmem h hh e he.1)
      refine runiq _ (hmem _ (inv_mem hh) _ h1) e he.1 ?_ ?_
      · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv]
      · rw [AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv]
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨h1, h2, h3⟩ := hrep _ (hmem _ (inv_mem hh) e he.1)
      refine runiq _ (hmem _ hh _ h1) e he.1 ?_ ?_
      · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv']
      · rw [AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv']
    · intro e he
      simp only [Finset.mem_filter] at he
      exact (hrep _ (hmem h hh e he.1)).2.1

  have hzn := T.prim n
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  have hζr : ∀ i : ℕ, T.ζ n ^ i = T.ζ n ^ (i % p ^ n) := fun i => by
    conv_lhs => rw [← Nat.mod_add_div i (p ^ n), pow_add, pow_mul, hzn.pow_eq_one, one_pow, mul_one]
  let Z : ℕ → Ω := fun i => Y (T.ζ n ^ i * r)
  have hZC : ∀ i, Z i ∈ C := by
    intro i
    refine ⟨int_sum _ _ fun e _ => int_gal e hy, fun h hh => ?_⟩
    rw [mem_Hfix] at hh
    show h (Y _) = Y _
    rw [hYgal h hh.1, map_mul, map_pow, (mem_Hinf.1 hh.1 n).1, hh.2]
  have hZmod : ∀ i i', i ≡ i' [MOD p ^ n] → Z i = Z i' := by
    intro i i' h
    show Y _ = Y _
    rw [(GlobalTheory.K5.Basic.zeta_pow_eq_iff T n i i').2 h]
  obtain ⟨a, ha⟩ := hK g hg
  have hZg : ∀ i, g (Z i) = Z (i + a) := by
    intro i
    show g (Y _) = Y _
    rw [hYgal g hg, map_mul, map_pow, (mem_Hinf.1 hg n).1, ha, pow_add, mul_assoc]
  have hZa : ∀ i, Z (i + a) - Z i ∈ I := fun i => by
    rw [← hZg]; exact Submodule.subset_span ⟨Z i, hZC i, rfl⟩
  have iter : ∀ b, (∀ i, Z (i + b) - Z i ∈ I) → ∀ t i, Z (i + t * b) - Z i ∈ I := by
    intro b hb t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      have e : i + (t + 1) * b = (i + t * b) + b := by ring
      rw [e]
      have := I.add_mem (hb (i + t * b)) (ih i)
      rwa [sub_add_sub_cancel] at this
  have hn : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    apply hgr
    rw [ha, hζr, hn0, pow_zero, Nat.mod_one, pow_zero, one_mul]
  have hna : ¬ p ^ n ∣ a := by
    intro hd
    apply hgr
    rw [ha, hζr, Nat.eq_zero_of_dvd_of_lt ?_ (Nat.mod_lt a hpos), pow_zero, one_mul]
    exact (Nat.dvd_mod_iff dvd_rfl).2 hd
  obtain ⟨k, hk⟩ := exists_mul_modEq_ppow hp hn hna
  have hZd : ∀ i, Z (i + p ^ (n - 1)) - Z i ∈ I := by
    intro i
    rw [hZmod (i + p ^ (n - 1)) (i + k * a) (Nat.ModEq.add_left i hk.symm)]
    exact iter a hZa k i
  set d := p ^ (n - 1) with hd
  set W := ∑ i ∈ Finset.range d, Z i with hW
  have hWC : W ∈ C := Subalgebra.sum_mem _ fun i _ => hZC i
  have hsumW : ∀ t : ℕ, ∑ i ∈ Finset.range (t * d), Z i - (t : Ω) * W ∈ I := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have e : (t + 1) * d = t * d + d := by ring
      rw [e, Finset.sum_range_add]
      have h2 : ∑ x ∈ Finset.range d, Z (t * d + x) - W ∈ I := by
        rw [hW, ← Finset.sum_sub_distrib]
        refine Submodule.sum_mem _ fun x _ => ?_
        rw [add_comm]; exact iter d hZd t x
      have := I.add_mem ih h2
      convert this using 1
      push_cast; ring
  have hNd : p * d = p ^ n := by
    rw [hd, ← pow_succ']; congr 1; omega
  have hsumZ : ∑ i ∈ Finset.range (p ^ n), Z i = T.ζ j - 1 := by
    rw [← hsum]
    have hinj : Set.InjOn (fun i => T.ζ n ^ i * r) (Finset.range (p ^ n) : Set ℕ) := by
      intro i hi i' hi' h
      simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
      exact hzn.pow_inj hi hi' (mul_right_cancel₀ hr0 h)
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r))
      (g := fun e : Gal p Ω => e r)]
    · rw [Finset.sum_image hinj]
    · intro e he
      obtain ⟨i, hi⟩ := hK e (hE' e he)
      rw [Finset.mem_image]
      exact ⟨i % p ^ n, Finset.mem_range.2 (Nat.mod_lt _ hpos), by rw [← hζr, hi]⟩
  have hτI : T.ζ j - 1 - (p : Ω) * W ∈ I := by
    have := hsumW p
    rwa [hNd, hsumZ] at this
  have hτ0 : T.ζ j - 1 ≠ 0 :=
    sub_ne_zero.2 ((T.prim j).ne_one (Nat.one_lt_pow (by omega) hp.one_lt))
  obtain ⟨hu0, huint⟩ := GlobalTheory.T.one_sub_prime_div_zeta_sub_one_mul_isUnit p hp2 Ω hΩ T j hj W hWC.1
  have huC : (1 - (p : Ω) / (T.ζ j - 1) * W)⁻¹ ∈ C := by
    refine ⟨huint, fun h hh => ?_⟩
    rw [mem_Hfix] at hh
    rw [map_inv₀, map_sub, map_one, map_mul, map_div₀, map_sub, map_one, map_natCast,
      (mem_Hinf.1 hh.1 j).1, hWC.2 h (by rw [mem_Hfix]; exact hh)]
  have := I.smul_mem (⟨_, huC⟩ : C) hτI
  rw [Subalgebra.smul_def, smul_eq_mul] at this
  have key : T.ζ j - 1 - (p : Ω) * W = (1 - (p : Ω) / (T.ζ j - 1) * W) * (T.ζ j - 1) := by
    have e2 : (p : Ω) / (T.ζ j - 1) * W * (T.ζ j - 1) = (p : Ω) * W := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hτ0]
    rw [sub_mul, one_mul, e2]
  rw [key, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul] at this
  exact this

end GlobalTheory.KumIdeal
end
end

