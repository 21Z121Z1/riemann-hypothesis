import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0716
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0755
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0772
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0773
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0774
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0775
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionFunctionLinearOnCells
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan

theorem sum_extend_smul_starLin {M : Type} [AddCommMonoid M] [Module ℝ M] {m m' : ℕ} (s : Fin m' ↪ Fin m)
    (d : Fin m' → ℝ) (f : Fin m → M) : ∑ i, Function.extend s d 0 i • f i = ∑ j, d j • f (s j) := by
  symm
  refine Fintype.sum_of_injective s s.injective _ _ (fun i hi => ?_) fun j => by rw [s.injective.extend_apply]
  rw [Function.extend_apply' _ _ _ hi]; simp

theorem extend_nonneg_starLin {m m' : ℕ} (s : Fin m' ↪ Fin m) {d : Fin m' → ℝ} (hd : ∀ j, 0 ≤ d j) (i : Fin m) :
    0 ≤ Function.extend s d 0 i := by
  by_cases hi : ∃ j, s j = i
  · obtain ⟨j, rfl⟩ := hi; rw [s.injective.extend_apply]; exact hd j
  · rw [Function.extend_apply' _ _ _ hi]; rfl

theorem starFun_linearOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (K D : ℕ), IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun H.bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun H.bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  intro E _ _ _ H q ψ w K D hcent
  refine ⟨?_, ?_⟩
  · intro X _ _ _ _ hX m γ hγ hno
    have ps0 : ∀ B ∈ rcone γ, evalR (starDepth H.bar ψ w) B = 0 := fun B hB =>
      le_antisymm (GlobalTheory.T.evalR_starDepth_le_of_centre_bound _ H.bar ψ w X m γ B 0 hγ hB le_rfl fun v hv hp hw hin _ _ _ =>
        absurd (hno v hv hp hin) (by rw [hw]; norm_num)) (starDepth_eval_nonneg _)
    have psγ : ∀ i, (starDepth H.bar ψ w).evalZ (γ i) = 0 := fun i => by
      rw [← evalR_toReal]; exact ps0 _ (inRCone_self γ i)
    rw [linearOn_iff]
    intro c hc
    rw [starFun_evalR, (linearOn_iff ψ γ).1 hγ.linear c hc, ps0 _ ⟨c, hc, rfl⟩, add_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [starFun_evalZ, psγ i]; ring
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hh
    obtain ⟨-, hC2, hC3⟩ := hcent X hX
    have uniq : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
      fun v hv hp hw hin => hC3 m γ hγ v hv hp β₀ hβ₀ hp₀ hw hw₀ hin hin₀
    have hne : β₀ ≠ 0 := by
      rintro rfl
      have := hC2 0 hβ₀ hp₀ hw₀ 2 0 (by simp)
      norm_num at this
    obtain ⟨e, he, hβe⟩ := id hin₀
    have coords : ∀ (a : ℝ) (d : Fin m' → ℝ), a • toReal β₀ + ∑ j, d j • toReal (γ (s j)) =
        ∑ i, (a * e i + Function.extend s d 0 i) • toReal (γ i) := fun a d => by
      rw [hβe, Finset.smul_sum, ← sum_extend_smul_starLin s d (fun i => toReal (γ i))]
      simp only [add_smul, mul_smul, Finset.sum_add_distrib]
    have hs0 : ∀ j, h (γ (s j)) = 0 := fun j => (hcut.2 (s j)).2 ⟨j, rfl⟩
    have psv : ∀ (a : ℝ) (d : Fin m' → ℝ), 0 ≤ a → (∀ j, 0 ≤ d j) →
        evalR (starDepth H.bar ψ w) (a • toReal β₀ + ∑ j, d j • toReal (γ (s j))) = a := by
      intro a d ha hd
      have hB : a • toReal β₀ + ∑ j, d j • toReal (γ (s j)) ∈ rcone γ :=
        ⟨fun i => a * e i + Function.extend s d 0 i,
          fun i => add_nonneg (mul_nonneg ha (he i)) (extend_nonneg_starLin s hd i), coords a d⟩
      refine le_antisymm (GlobalTheory.T.evalR_starDepth_le_of_centre_bound _ H.bar ψ w X m γ _ a hγ hB ha fun v hv hp hw hin t ht hBt => ?_)
        (GlobalTheory.T.centreDepth_le_starDepth_of_cell _ H.bar ψ w X m γ _ β₀ a hγ hB hβ₀ hp₀ hw₀ hin₀ hne uniq ha ?_)
      · rw [uniq v hv hp hw hin] at hBt
        obtain ⟨g, hg, hBg⟩ := hBt
        have rel := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) h
          (β := Sum.elim (fun j => γ (s j)) (fun o : Option (Fin m) => o.elim β₀ γ))
          (c := Sum.elim d (fun o : Option (Fin m) => o.elim (a - t) fun i => -g i)) (by
            simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim,
              LinearMap.id_apply, neg_smul, Finset.sum_neg_distrib]
            rw [← hBg, sub_smul]
            abel)
        simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim,
          hs0, Int.cast_zero, mul_zero, Finset.sum_const_zero, zero_add, neg_mul, Finset.sum_neg_distrib] at rel
        have hpos : 0 ≤ ∑ i, g i * (h (γ i) : ℝ) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (by exact_mod_cast hcut.1 i)
        have hh' : (0 : ℝ) < h β₀ := by exact_mod_cast hh
        nlinarith
      · exact ⟨Function.extend s d 0, extend_nonneg_starLin s hd, by
          rw [add_sub_cancel_left, sum_extend_smul_starLin]⟩
    have psβ : (starDepth H.bar ψ w).evalZ β₀ = 1 := by
      have := psv 1 0 zero_le_one fun _ => le_rfl
      simpa using this
    have psγs : ∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0 := fun j => by
      have := psv 0 (Pi.single j 1) le_rfl fun i => by by_cases hi : i = j <;> simp [Pi.single_apply, hi]
      simpa [Pi.single_apply] using this
    have ψv : ∀ (a : ℝ) (d : Fin m' → ℝ), 0 ≤ a → (∀ j, 0 ≤ d j) →
        evalR ψ (a • toReal β₀ + ∑ j, d j • toReal (γ (s j))) = a * ψ.evalZ β₀ + ∑ j, d j * ψ.evalZ (γ (s j)) := by
      intro a d ha hd
      have hψβ : ψ.evalZ β₀ = ∑ i, e i * ψ.evalZ (γ i) := by
        rw [← evalR_toReal, hβe, (linearOn_iff ψ γ).1 hγ.linear e he]
      have hx := sum_extend_smul_starLin s d fun i => ψ.evalZ (γ i)
      simp only [smul_eq_mul] at hx
      rw [coords, (linearOn_iff ψ γ).1 hγ.linear _
        (fun i => add_nonneg (mul_nonneg ha (he i)) (extend_nonneg_starLin s hd i)), hψβ, Finset.mul_sum, ← hx]
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib]
    rw [linearOn_iff]
    intro c hc
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [starFun_evalR, ψv _ _ (hc 0) (fun j => hc _), psv _ _ (hc 0) (fun j => hc _), starFun_evalZ, psβ]
    simp only [starFun_evalZ, psγs, add_zero]
    have e1 : ∑ j : Fin m', c j.succ * ((D : ℝ) * (K * ψ.evalZ (γ (s j)))) =
        D * K * ∑ j : Fin m', c j.succ * ψ.evalZ (γ (s j)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1]; ring

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceSquare
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory

set_option maxHeartbeats 4000000 in
open GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.BigTop.Fun in

theorem Mem.LiteralAutomorphy.trSq_holds : GlobalTheory.Mem.LiteralAutomorphy.TrSq := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ hs
  obtain ⟨⟨hpre, -, -, ⟨f, f', hff, hC, hC'⟩, hbase, hxi, -, -⟩, hg, -, -⟩ := h
  clear S S' W W'
  obtain ⟨B, C₁, W₁, V₁, S₁, N₁, G₁⟩ := X
  obtain ⟨B', C₂, W₂, V₂, S₂, N₂, G₂⟩ := X'
  cases B; cases B'
  dsimp only at hpre
  subst hpre
  obtain rfl := eq_of_heq hff
  have hv0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hg.v0
  have hw : G'.pl.w = G.pl.w := eq_of_heq hg.w
  have hchi : G'.ch.chiH = G.ch.chiH := eq_of_heq hg.chiH
  have hx : L'.xiH μ₀' = L.xiH μ₀ := by have := eq_of_heq (hxi μ₀'); rwa [hbase] at this
  have e_levQ : levQ G'.pl = levQ G.pl := by
    unfold levQ Places.S0 condExp; rw [hv0]; exact (Eq.refl (levQ G.pl))
  have e_condE : SqNum.condE G'.pl = SqNum.condE G.pl := by
    unfold SqNum.condE Places.S0 condExp; rw [hv0, hw]; exact (Eq.refl (SqNum.condE G.pl))
  have e_condF : condF G'.pl = condF G.pl := by
    unfold condF Places.S0 condExp; rw [hv0]; exact (Eq.refl (condF G.pl))
  have hmu : L'.C.mu0 = L.C.mu0 := by rw [hC, hC']; exact (Eq.refl f'.mu0)
  have heta : L'.C.eta = L.C.eta := by rw [hC, hC']; exact (Eq.refl f'.eta)
  have hd1 : L'.C.del = L.C.del := by rw [hC, hC']; exact (Eq.refl f'.del)
  have hd2 : L'.C.del' = L.C.del' := by rw [hC, hC']; exact (Eq.refl f'.del')
  have e_nu : ∀ i j, nuH G' μ₀' i j = nuH G μ₀ i j := by
    intro i j; unfold nuH; rw [hmu, hx, hchi]; exact (Eq.refl (nuH G μ₀ i j))
  have e_beta : ∀ i j, betaH G' i j = betaH G i j := by
    intro i j; unfold betaH; rw [heta, hchi]; exact (Eq.refl (betaH G i j))
  have e_alpha : ∀ i j, alphaH L' μ₀' i j = alphaH L μ₀ i j := by
    intro i j; unfold alphaH; rw [hmu, hx, heta]; exact (Eq.refl (alphaH L μ₀ i j))
  have e_del : ∀ c, delOf L' c = delOf L c := by
    intro c; unfold delOf; rw [hd1, hd2]; exact (Eq.refl (delOf L c))
  have eT : ∀ i j s χ x, IsTor G' i j s χ x ↔ IsTor G i j s χ x := by
    intro i j s χ x; unfold IsTor; rw [e_condF]; exact (Iff.refl (IsTor G i j s χ x))

  let hk1 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt1 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk1 w.chV, chV' := hk1 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt1 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt1 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  let hk2 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt2 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk2 w.chV, chV' := hk2 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt2 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt2 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  have btr1 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q), IsBottom G μ₀ i j (SqNum.condE G.pl) P P' →
        IsBottom G' μ₀' i j (SqNum.condE G'.pl) (pt1 P) (pt1 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨(h1), ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_beta, e_nu]; exact (h2)
    · rw [e_alpha, e_nu]; exact (h3)
    · rw [e_condE]; exact (h4)
    · rw [e_condE]; exact (h5)
    · rw [e_condE]; exact (h6)

  have btr2 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q), IsBottom G' μ₀' i j (SqNum.condE G'.pl) P P' →
        IsBottom G μ₀ i j (SqNum.condE G.pl) (pt2 P) (pt2 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    rw [e_beta, e_nu] at h2
    rw [e_alpha, e_nu] at h3
    rw [e_condE] at h4 h5 h6
    exact ⟨(h1), (h2), (h3), (h4), (h5), (h6)⟩
  refine ⟨fun hb => ?_, fun i j s c x y h1 h2 h3 h4 => ?_⟩
  · obtain ⟨δ, t0, hb⟩ := hb
    rw [e_levQ] at hb
    obtain ⟨δ', t0', hb'⟩ := hs.norms ⟨δ, t0, fun ij => by
      obtain ⟨P, P', hP, -, -⟩ := hb ((ij))
      exact ⟨pt2 P, pt2 P', btr2 ((ij.1)) ((ij.2)) P P' hP, trivial, trivial⟩⟩
    refine ⟨δ', t0', fun ij => ?_⟩
    rw [e_levQ]
    obtain ⟨P, P', hP, n1, n2⟩ := hb' ((ij))
    exact ⟨pt1 P, pt1 P', btr1 ij.1 ij.2 P P' hP, (n1), (n2)⟩
  · rw [eT, e_nu] at h3
    rw [eT, e_nu, e_del] at h4
    exact hs.toric ((i)) ((j)) s c x y h1 ((h2)) ((h3)) ((h4))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsAvoidExcludedPrimesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistConductors_avoid_excludedPrimes : AllSt fun _ _ _ T _ _ x => ∀ v, ∀ u ∈ T.Q v, ∀ p ∈ lowAll (Dof x), u ∉ placesOver (Dof x).host.E p := by
  first | exact @GlobalTheory.LowAvoid.conductors_avoid_lowAll | exact GlobalTheory.LowAvoid.conductors_avoid_lowAll | (intros; apply GlobalTheory.LowAvoid.conductors_avoid_lowAll <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistReadingInducesSideEmbeddingFixedFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), GlobalTheory.HeightCounting.SidePl D v i b ∧ (∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x))) ∧ ∀ (h : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp ((algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))))) (x : ↥D.LL0), ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) h (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := by
  first | exact @GlobalTheory.LevCmp.reading_sidePl_emb | exact GlobalTheory.LevCmp.reading_sidePl_emb | (intros; apply GlobalTheory.LevCmp.reading_sidePl_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceLocalIndex
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.LocEx

theorem atMem_imp {hL : GlobalTheory.Published.LocalLanglandsGL} {p q : LayP hL} (h : AtMem hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : AtMem hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)

theorem exists_loc_of_thetaT {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M) {v : D.what₂.places.Pl} (hv : TwistedAt D v) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hne : ∃ f, D.what₂.thetaT (D.what₂.muTw v) j f ≠ 0) :
    ∃ i : D.nd.Loc, D.nd.w i = v ∧ D.nd.j i = j := by
  obtain ⟨f, hf⟩ := hne
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)
  have hidx : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h3 := (D.what₂.jMt_basis (D.what₂.muTw v) j b).2
    rw [Set.range_eq_empty, Submodule.span_empty] at h3
    exact hf ((Submodule.mem_bot ℂ).1 (h3 ▸ Submodule.mem_top))
  obtain ⟨k⟩ := hidx
  haveI : Nontrivial (T.B.V j v) := ⟨⟨_, 0, (T.B.iV_basis j v b).1.ne_zero k⟩⟩
  haveI : Nontrivial (Formalism.L2.heckeAlg T.B j v) := inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Formalism.L2.heckeAlg T.B j v)
  obtain ⟨i, hi, -⟩ := T.mx_all j v h1 h2 hv I hI
  obtain ⟨ej, ew⟩ := (D.nd.locs_mem _ _ _).1 hi
  exact ⟨i, ew, ej⟩

theorem thetaT_ne_of_lamTr {D : D7} {μ : D.what₂.Tup} {j : ℕ} {σ : D.what₂.FT} (hpos : 0 < DV.lamTr D μ j σ) :
    ∃ f ∈ D.what₂.isot j σ, D.what₂.thetaT μ j f ≠ 0 := by
  by_contra h
  push_neg at h
  have hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ ((D.what₂.isot j σ).starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) = 0 := by
    ext y
    simp [h _ ((D.what₂.isot j σ).starProjection_apply_mem y)]
  unfold DV.lamTr at hpos
  rw [hT, map_zero, Complex.zero_re, zero_div] at hpos
  exact lt_irrefl _ hpos

theorem exists_loc : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → ∃ i : (w.D Z).nd.Loc, (w.D Z).nd.w i = v ∧ (w.D Z).nd.j i = j :=
  fun hP hL => atMem_imp (GlobalTheory.T.twisted_place_weight_positive hP hL) fun _ _ _ _ w Z _ _ t _ _ c h v hv j h1 h2 σ hσ => by
    have hl := h v hv j h1 h2 σ hσ
    obtain ⟨f, -, hf⟩ := thetaT_ne_of_lamTr (D := w.D Z) (hl.trans_eq (t.r.Y.lam _ j h1 h2 σ hσ))
    exact exists_loc_of_thetaT c.a.all.cover hv h1 h2 ⟨f, hf⟩

end GlobalTheory.HeightCounting.Up.LocEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleFiniteOrderPartUnramifiedAtTypePrimeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTuple_finiteOrderPart_unramified_at_typePrimes : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (v : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E)) (k : Fin 2),
    ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal → Q ∉ T.Q v → (T.xiTw f v).UnrAt Q := by
  first | exact @GlobalTheory.TwistUnr.unrAt_xiTw | exact GlobalTheory.TwistUnr.unrAt_xiTw | (intros; apply GlobalTheory.TwistUnr.unrAt_xiTw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistsAtLinked
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)

theorem cond_powers {D : D7} {C : NChoice D} {I : TwIn D} (h : DQ.GoodAllAt D C I) :
    (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (C.twI w) (C.Q w)) ∧
    ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (C.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (C.twI w) (C.Q w) (C.k' w) (C.psi' w ^ a) (twEps D (C.twI w)) := by
  classical
  refine ⟨fun w hw => ?_, I.N0, fun w hw a ha => ?_⟩
  · have h1 := ((h w hw).2 1 (by simp)).1
    exact ⟨fun P hP => (h1.1 P hP).1, (Finset.disjoint_union_right.1 h1.2.1).1,
      GlobalTheory.AntiRam.ramExactly_conj D _ _ _ h1.2.2.2.2.1 h1.2.2.2.2.2.2.1⟩
  · have e : ∃ b : ℤ, b.natAbs = a.natAbs ∧ BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w ^ b) = C.psi' w ^ a := by
      cases C.sd w
      · exact ⟨-a, Int.natAbs_neg a, by simp [BlochKatoReduction.Gen.psiAt]⟩
      · exact ⟨a, rfl, by simp [BlochKatoReduction.Gen.psiAt]⟩
    obtain ⟨b, hb, e⟩ := e
    have hc : Nat.Coprime b.natAbs (D.ntw.l (C.twI w)) := by
      rw [hb]
      simpa using Int.isCoprime_iff_nat_coprime.1 ha
    exact e ▸ ((h w hw).2 b hc).2.2.2.2.1

theorem twI_eq {D : D7} {C : NChoice D} {xd : ThData D} (h : GoodO D C xd) {w w' : D.what₂.places.Pl}
    (hw : Twisted D w) (hw' : Twisted D w') (e : C.Q w = C.Q w') (hne : C.Q w ≠ ∅) : C.twI w = C.twI w' := by
  by_contra hn
  have := h.sep w w' hw hw' hn
  rw [← e] at this
  exact hne (disjoint_self.1 this)

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

theorem Q_eq (q : WPt p.s K) {w w' : (q.w.D q.Z).what₂.places.Pl} (hw : Twisted (q.w.D q.Z) w)
    (hw' : Twisted (q.w.D q.Z) w') (h : SamePair (q.w.D q.Z) w w') :
    q.O.ex.nch.Q w = q.O.ex.nch.Q w' ∧ q.O.ex.nch.k' w = q.O.ex.nch.k' w' := by
  have key : ∀ v v', Twisted (q.w.D q.Z) v → Twisted (q.w.D q.Z) v' → SameBelow (q.w.D q.Z) v v' →
      q.O.ex.nch.Q v = q.O.ex.nch.Q v' ∧ q.O.ex.nch.k' v = q.O.ex.nch.k' v' := by
    intro v v' hv hv' hs
    have m : ∀ u, Twisted (q.w.D q.Z) u → u ∈ q.x.Wt := fun u hu => by
      by_contra hn
      exact hu (q.x.what₂.mu.off u hn)
    have a := q.x.n.Q v (m v hv)
    have a' := q.x.n.Q v' (m v' hv')
    have c := q.x.coh.same v v' fun x hx => hs ⟨x, hx⟩
    exact ⟨a.1.trans (c.1.trans a'.1.symm), a.2.trans (c.2.1.trans a'.2.symm)⟩
  rcases h with h | h
  · exact key w w' hw hw' h
  · have k := key _ w' ((GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw) hw' h
    have c := q.core.a.all.choice.conj w hw
    exact ⟨(congrArg (fun t : TwPack _ => t.2.1) c).symm.trans k.1, (congrArg (fun t : TwPack _ => t.2.2.1) c).symm.trans k.2⟩

theorem twists_at_linked : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) (Q : V4.Slot), RowE Q (IsLinked p) fun _ D O _ _ => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w)) := by
  intro hL p Q
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', -, he⟩ := hl
  have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c =>
    (fun (D : D7) (O : Obj D) => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w))) s.1 s.2.1) he
  refine cast h1.symm ?_
  obtain ⟨I, -, hI, -⟩ := q.x.good.tw
  exact ⟨fun w hw => ⟨q.O.ex.nch.twI_l w, GlobalTheory.TwistGoodCompare.atPlace_of_tie q.B.coeffGaloisSubfield_isGalois q.O.ex.nch_tie w hw⟩,
    fun w w' hw hw' h => ⟨(Q_eq q hw hw' h).1, (Q_eq q hw hw' h).2, twI_eq q.x.good hw hw' (Q_eq q hw hw' h).1⟩, cond_powers hI⟩

end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlacesUnionRamifiedPlacesFiniteStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_union_ramifiedPlaces_finite : ∀ (D : D7) (η : HChar D.host.E), (gPl D ∪ qPl D η).Finite := by
  first | exact @GlobalTheory.LevCmp.gPl_union_qPl_finite | exact GlobalTheory.LevCmp.gPl_union_qPl_finite | (intros; apply GlobalTheory.LevCmp.gPl_union_qPl_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueLocalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.types_true_local : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ _ => TypesTrue (w.D Z).ntypes t.r.z.R.C.P t.r.z.R.C.W := by
  first | exact @GlobalTheory.HeightCounting.Up.TypesAt.types_atMem | exact GlobalTheory.HeightCounting.Up.TypesAt.types_atMem | (intros; apply GlobalTheory.HeightCounting.Up.TypesAt.types_atMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentHolomorphicBoundedDomainStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationComponent_holomorphic_boundedDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (W : X.X.Opens) (g : Γ(X.X, W)), DifferentiableOn ℂ (ev X.str (σ.comp e.toRingHom) W g ∘ ψ) (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W) := by
  first | exact @GlobalTheory.UnifHolo.holo | exact GlobalTheory.UnifHolo.holo | (intros; apply GlobalTheory.UnifHolo.holo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricLowerDetUnitAndSuperdiagIntegralStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), NG.ParaRT s r h → Valued.v (NG.detDD s r h) = 1 ∧ Valued.v (NG.supDiag s r h) ≤ 1 := by
  first | exact @GlobalTheory.ParaUnit.detDD_unit_supDiag_int | exact GlobalTheory.ParaUnit.detDD_unit_supDiag_int | (intros; apply GlobalTheory.ParaUnit.detDD_unit_supDiag_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivisionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witnesses_pass_along_set_division : ∀ 𝒮 : Slots, PositionMv 𝒮 → WitMv 𝒮 := by
  first | exact @GlobalTheory.Mem.Top.Bl.witMv_of_positionMv | exact GlobalTheory.Mem.Top.Bl.witMv_of_positionMv | (intros; apply GlobalTheory.Mem.Top.Bl.witMv_of_positionMv <;> assumption)
end

