import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0017
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0049
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0032
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameThetaConstPos

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTorusAtOfIsTorusOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OrthoPeriodTorus

section

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r) (x : FD.Frame X.Ψ r)

theorem perFr_add (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.Pj.perFr X x (v + w) τ i = Formalism.L2.Pj.perFr X x v τ i + Formalism.L2.Pj.perFr X x w τ i := by
  have he : ∀ ρ : E →+* ℂ, Data.emb ρ (v + w) = Data.emb ρ v + Data.emb ρ w := by
    intro ρ
    funext a
    simp [Data.emb]
  unfold Formalism.L2.Pj.perFr
  rw [he, he]
  split_ifs
  · simp [Matrix.mulVec_add]
  · simp
  · simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  · simp
  · simp

theorem perFr_smul (α : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.Pj.perFr X x (α • v) τ i = τ α * Formalism.L2.Pj.perFr X x v τ i := by
  have he : ∀ ρ : E →+* ℂ, Data.emb ρ (α • v) = ρ α • Data.emb ρ v := by
    intro ρ
    funext a
    simp [Data.emb]
  have hc : (starRingEnd ℂ) ((conjEmb τ) α) = τ α := by
    simp [conjEmb]
  unfold Formalism.L2.Pj.perFr
  rw [he, he]
  split_ifs
  · simp [Matrix.mulVec_smul]
  · simp
  · simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · simp
  · simp

theorem norm_sq_eq_Hf {J : Type} [Fintype J] (v : EuclideanSpace ℂ J) : ‖v‖ ^ 2 = (I2.Hf v v).re := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [I2.Hf, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end

theorem isTorusAt_of_isTorusOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W) (T : I2.PT E) (ψ : (Fin W.g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), GoodEmb c σ → IsUnf U → (U.X k).IsOrtho x.1 → IsTorusOf (W.F.Di (W.ik k)) (fun j => relab c σ (W.e j).1) W.Pm Wu.Hm T ψ → I2.IsTorusAt (U.X k) x.1 T ∧ T.r = r ∧ ∀ th, T.ph th = I2.phiFD (U.X k) th x.1 := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu T ψ hg hu ho ht
  classical
  have hU := hu
  unfold Formalism.L2.Pj.IsUnf at hU
  obtain ⟨hr, hPsi, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := hPsi k
  obtain ⟨hbij0, hrt0, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hg
  have hrel : Formalism.L2.PjFree.relab c σ = relab c σ := funext fun τ => rfl
  have hbij : Function.Bijective (relab c σ) := by
    rw [← hrel]
    exact hbij0
  have hrt : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := by
    intro τ
    rw [← hrel]
    exact hrt0 τ
  unfold GlobalTheory.EtaAn.IsTorusOf at ht
  obtain ⟨hTr, -, hHf, hL, hact, -⟩ := ht
  have hsig := W.F.sig (W.ik k)
  have hle := (U.X k).p0_le
  have hcc : ∀ ρ : E →+* ℂ, NumberField.ComplexEmbedding.conjugate (conjEmb ρ) = ρ := by
    intro ρ
    ext y
    simp [conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hcc2 : ∀ ρ : E →+* ℂ, conjEmb (conjEmb ρ) = ρ := by
    intro ρ
    ext y
    simp [conjEmb]
  have hconjMem : ∀ ρ : E →+* ℂ, ρ ∉ (U.X k).Ψ → conjEmb ρ ∈ (U.X k).Ψ := by
    intro ρ hρ
    rw [(U.X k).cmType, hcc]
    exact hρ
  have hmultP : ∀ τ' : E →+* ℂ, relab c σ τ' ∈ (U.X k).Ψ → Dw.mult τ' = Dw.p := by
    intro τ' h
    have h' : τ' (H.rt : E) = H.rt0 := (hrt τ').1 ((hΨ _).1 h)
    simp [Datum.mult, h']
  have hmultN : ∀ τ' : E →+* ℂ, relab c σ τ' ∉ (U.X k).Ψ → Dw.mult τ' = Dw.q := by
    intro τ' h
    have h' : ¬ τ' (H.rt : E) = H.rt0 := fun h'' => h ((hΨ _).2 ((hrt τ').2 h''))
    simp [Datum.mult, h']
  let fwd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → (U.X k).Ψ × Fin r := fun s =>
    if h : relab c σ s.1 ∈ (U.X k).Ψ then
      (⟨relab c σ s.1, h⟩, ⟨(U.X k).p0 + s.2, by have := s.2.isLt; have := hmultP _ h; omega⟩)
    else
      (⟨conjEmb (relab c σ s.1), hconjMem _ h⟩,
        ⟨(U.X k).p0 - 1 - s.2, by have := s.2.isLt; have := hmultN _ h; omega⟩)
  have hfwd : Function.Bijective fwd := by
    constructor
    · rintro ⟨τ1, i1⟩ ⟨τ2, i2⟩ heq
      have hi1 := i1.isLt
      have hi2 := i2.isLt
      by_cases h1 : relab c σ τ1 ∈ (U.X k).Ψ <;> by_cases h2 : relab c σ τ2 ∈ (U.X k).Ψ
      · simp only [fwd, dif_pos h1, dif_pos h2, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at heq
        obtain ⟨he1, he2⟩ := heq
        obtain rfl := hbij.1 he1
        obtain rfl : i1 = i2 := Fin.ext (by omega)
        rfl
      · simp only [fwd, dif_pos h1, dif_neg h2, Prod.mk.injEq, Fin.mk.injEq] at heq
        have := hmultN _ h2
        omega
      · simp only [fwd, dif_neg h1, dif_pos h2, Prod.mk.injEq, Fin.mk.injEq] at heq
        have := hmultN _ h1
        omega
      · simp only [fwd, dif_neg h1, dif_neg h2, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at heq
        obtain ⟨he1, he2⟩ := heq
        have hρ : relab c σ τ1 = relab c σ τ2 := by
          have h3 := congrArg conjEmb he1
          rwa [hcc2, hcc2] at h3
        obtain rfl := hbij.1 hρ
        have := hmultN _ h1
        obtain rfl : i1 = i2 := Fin.ext (by omega)
        rfl
    · rintro ⟨⟨ρ, hρ⟩, t⟩
      obtain ⟨τ', rfl⟩ := hbij.2 ρ
      by_cases ht0 : (U.X k).p0 ≤ (t : ℕ)
      · refine ⟨⟨τ', ⟨t - (U.X k).p0, by have := hmultP _ hρ; have := t.isLt; omega⟩⟩, ?_⟩
        simp only [fwd, dif_pos hρ]
        refine Prod.ext (Subtype.ext rfl) (Fin.ext ?_)
        show (U.X k).p0 + ((t : ℕ) - (U.X k).p0) = t
        omega
      · obtain ⟨τ'', hτ''⟩ := hbij.2 (conjEmb (relab c σ τ'))
        have hn : relab c σ τ'' ∉ (U.X k).Ψ := by
          rw [hτ'']
          intro hm
          rw [(U.X k).cmType, hcc] at hm
          exact hm hρ
        refine ⟨⟨τ'', ⟨(U.X k).p0 - 1 - t, by have := hmultN _ hn; omega⟩⟩, ?_⟩
        simp only [fwd, dif_neg hn]
        refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · show conjEmb (relab c σ τ'') = relab c σ τ'
          rw [hτ'', hcc2]
        · show (U.X k).p0 - 1 - ((U.X k).p0 - 1 - (t : ℕ)) = t
          omega
  let idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans (Equiv.ofBijective fwd hfwd)
  have hP : ∀ a j, W.Pm a j = GlobalTheory.RiemMaj.pc (U.X k) x.1 (W.φ k a : Fin r → E) (idx j) := by
    intro a j
    rw [W.pm_eq a j]
    show _ = GlobalTheory.RiemMaj.pc (U.X k) x.1 _ (fwd (W.e j))
    generalize W.e j = s
    obtain ⟨τ', i⟩ := s
    have hi := i.isLt
    by_cases h : relab c σ τ' ∈ (U.X k).Ψ
    · have := hmultP _ h
      have hlt : (U.X k).p0 + (i : ℕ) < r := by omega
      have hnlt : ¬ (U.X k).p0 + (i : ℕ) < (U.X k).p0 := by omega
      simp only [fwd, dif_pos h]
      unfold Formalism.L2.Pj.perFr GlobalTheory.RiemMaj.pc
      simp only [dif_pos h, dif_pos hlt, hnlt, if_false]
    · have := hmultN _ h
      have hc := hconjMem _ h
      have hlt : (U.X k).p0 - 1 - (i : ℕ) < r := by omega
      have hlt' : (U.X k).p0 - 1 - (i : ℕ) < (U.X k).p0 := by omega
      simp only [fwd, dif_neg h]
      unfold Formalism.L2.Pj.perFr GlobalTheory.RiemMaj.pc
      simp only [dif_neg h, dif_pos hc, dif_pos hlt, hlt', if_true]
  have him : ∀ a b, (hermForm Wu.Hm (W.Pm a) (W.Pm b)).im =
      ((Algebra.trace ℚ E (-(U.X k).ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (W.φ k a : Fin r → E) (W.φ k b)) : ℚ) : ℝ) := by
    intro a b
    rw [Wu.c1 a b]
    exact_mod_cast W.isom k a b
  have hcore := GlobalTheory.RiemMaj.core (U.X k) x.2 idx (fun a => (W.φ k a : Fin r → E)) W.Pm hP
    W.per.2.2.2.1 Wu.Hm Wu.pos him
  let per : (Fin r → E) → Fin W.g → ℂ := fun v j =>
    Formalism.L2.Pj.perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2
  have per_add : ∀ v w, per (v + w) = per v + per w := fun v w =>
    funext fun j => perFr_add (U.X k) x.1 v w _ _
  let φ : (Fin r → E) →+ I2.Vsp T.dim := AddMonoidHom.mk' (fun v => ψ (per v)) (by
    intro v w
    show ψ (per (v + w)) = ψ (per v) + ψ (per w)
    rw [per_add, map_add])
  have hφa : ∀ a, φ (W.φ k a : Fin r → E) = ψ (W.Pm a) := by
    intro a
    show ψ (per _) = _
    congr 1
    funext j
    exact (W.pm_eq a j).symm
  have hmem : ∀ v ∈ (U.X k).Λ, ∃ a, (W.φ k a : Fin r → E) = v := fun v hv =>
    ⟨(W.φ k).symm ⟨v, hv⟩, by simp⟩
  have hTA : I2.IsTorusAt (U.X k) x.1 T := by
    refine ⟨φ, -1, Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · intro y
      rw [hL y]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, (W.φ k a).2, hφa a⟩
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨a, rfl⟩ := hmem v hv
        exact ⟨a, (hφa a).symm⟩
    · intro α v
      show ψ (per _) = I2.act α (ψ (per v))
      rw [← hact α (per v)]
      congr 1
      funext j
      exact perFr_smul (U.X k) x.1 (α : E) v _ _
    · intro v hv
      obtain ⟨a, rfl⟩ := hmem v hv
      rw [hφa, norm_sq_eq_Hf, hHf]
      exact hcore.1 a
    · intro u hu' v hv
      obtain ⟨a, rfl⟩ := hmem u hu'
      obtain ⟨b, rfl⟩ := hmem v hv
      rw [hφa, hφa, hHf, him a b, neg_mul, map_neg]
      push_cast
      ring
  refine ⟨hTA, ?_, fun th => (ReciprocityTheory.ChartRestriction.G.I2.TorusAtPf.torusAtLa1_holds E r (U.X k) x.1 x.2 T hTA).2 th⟩
  rw [hTr, hsig.1, hsig.2]
  exact hr.symm

end GlobalTheory.OrthoPeriodTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicSumIndependentOfChoicesLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem shortSum_toΓ_injective (S : Type) [CommRing S] : Function.Injective (toΓ S) := by
  intro a b h
  have hinv : ∀ x : S, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (toΓ S x) = x := by
    intro x
    unfold toΓ
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  rw [← hinv a, ← hinv b, h]

private theorem eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one {M : Type*} [CommMonoid M] (x : M) (N : ℕ) (hN : Odd N)
    (h2 : x ^ 2 = 1) (hN2 : x ^ (N ^ 2) = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hN.pow (n := 2)
  rw [hk, pow_succ, pow_mul, h2, one_pow, _root_.one_mul] at hN2
  exact hN2

set_option maxHeartbeats 1000000 in

theorem shortSum_indep_local : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (P : MvPolynomial (LtN Dw n) c.F) (T : Type) [CommRing T] [IsLocalRing T] [Algebra c.F T] (y : FrPt Xo c T) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ q, ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F1 q i b) (colOf m b) = ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b) := by
  intro hL E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hTr hLev P T _ _ _ y z1 tp1 F1 z2 tp2 F2 hz1 hg1 htp1 hF1 hz2 hg2 htp2 hF2 q
  obtain ⟨hNodd, hMN, hNL⟩ := hLev
  have hN0 : 0 < N := hNodd.pos
  have hLa : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hNL.trans inf_le_left
  have hsurj := (GlobalTheory.T.isotropic_enumeration_surjective_local_ring hL E H Dw l Xo T y.x n Λ N hU hN0 hLa z1 hz1 hg1).1
  have h58 := GlobalTheory.T.torsion_isotropic_commutator_pairing hL E H Dw l Xo T y.x n Λ N hU hN0 hLa
  have h56 := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  have h57 := (GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique hL E H Dw l Xo N hN0).2.1

  have hz2inj : Function.Injective z2 := by
    intro i i' h
    let g : ptO Xo (spMap (IsLocalRing.residue T) ≫ y.x) ⟶ ptO Xo y.x :=
      Over.homMk (spMap (IsLocalRing.residue T)) rfl
    exact hg2 (IsLocalRing.ResidueField T) (IsLocalRing.residue T) g rfl
      (congrArg (fun (w : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (b : Fin n) => g ≫ w b) h)

  obtain ⟨u, hu⟩ : ∃ u : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G), ∀ b, u b = (tp1 q b)⁻¹ * tp2 q b :=
    ⟨_, fun _ => rfl⟩
  have htp : ∀ b, tp2 q b = tp1 q b * u b := fun b => by
    rw [hu, mul_inv_cancel_left]
  have hlev : ∀ a : Dw.La, levPt Xo y.x a ^ N = 1 := by
    intro a
    obtain ⟨k, hk⟩ := hMN
    unfold levPt
    rw [← MonObj.comp_pow, hk, pow_mul, (GlobalTheory.moduli_univ_eta_killed hL E H Dw l Xo a).2.2, one_pow,
      MonObj.comp_one]
  have hu1 : ∀ b, u b ^ N = 1 := fun b => by
    rw [hu, mul_pow, inv_pow, (htp1 q b).1, (htp2 q b).1, inv_mul_cancel]
  have hsq : ∀ x : ptO Xo y.x ⟶ Xo.univ.t.G, x ^ N = 1 → x ^ (N ^ 2) = 1 := fun x hx => by
    rw [sq, pow_mul, hx, one_pow]
  have ht2 : ∀ b, tp1 q b ^ (N ^ 2) = 1 := fun b => by
    rw [sq, pow_mul, (htp1 q b).1, hlev]
  have hkill : ∀ b, ∃ j, KilledBy Xo (l.Mb ^ j) (tp1 q b) ∧ KilledBy Xo (l.Mb ^ j) (u b) := by
    intro b
    obtain ⟨j1, hj1⟩ := (htp1 q b).2
    obtain ⟨j2, hj2⟩ := (htp2 q b).2
    have mono : ∀ {i j : ℕ} (t : ptO Xo y.x ⟶ Xo.univ.t.G), i ≤ j →
        KilledBy Xo (l.Mb ^ i) t → KilledBy Xo (l.Mb ^ j) t :=
      fun t hij ht a ha => ht a (Ideal.pow_le_pow_right hij ha)
    refine ⟨max j1 j2, mono _ (le_max_left _ _) hj1, ?_⟩
    intro a ha
    have := Xo.univ.t.act.hom a
    have k1 := mono _ (le_max_left _ _) hj1 a ha
    have k2 := mono _ (le_max_right _ _) hj2 a ha
    have h1 : ((tp1 q b)⁻¹ ≫ Xo.univ.t.act.act a) * (tp1 q b ≫ Xo.univ.t.act.act a) = 1 := by
      rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
    rw [k1, _root_.mul_one] at h1
    rw [hu, MonObj.mul_comp, h1, k2, _root_.one_mul]
  have hInU : InZh Xo Λ N u := h56.2.2.2 hTr (ptO Xo y.x) u (fun b => by
    obtain ⟨j, -, hj⟩ := hkill b
    exact ⟨hu1 b, j, hj⟩)

  have hw : ∀ i, ∃ j, z1 j = fun b => u b * z2 i b := fun i =>
    hsurj _ (h56.2.1 _ u (z2 i) hInU (hz2 i))
  choose ρ hρ using hw
  have hρinj : Function.Injective ρ := by
    intro i i' h
    apply hz2inj
    funext b
    have hii := (hρ i).symm.trans ((congrArg z1 h).trans (hρ i'))
    exact mul_left_cancel (show u b * z2 i b = u b * z2 i' b from congrFun hii b)
  have hρbij : Function.Bijective ρ := Finite.injective_iff_bijective.mp hρinj

  have key : ∀ i, (∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) (colOf m b) := by
    intro i
    have he : ∀ b, ∃ e : Γ((ptO Xo y.x).left, ⊤)ˣ,
        WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (u b) (z2 i b) e := fun b =>
      (h57 (ptO Xo y.x) (u b) (z2 i b) (hsq _ (hu1 b)) ((hz2 i).1 b)).imp fun _ h => h.1
    choose e he using he
    have hpe : ∏ b, e b = 1 := h58.1 u (z2 i) e hInU (hz2 i) he
    have hr : ∀ b, ∃ r : T, (toΓ T r) ^ 2 = ((e b : Γ((ptO Xo y.x).left, ⊤))) ∧ r ^ (N ^ 2) = 1 ∧
        ∀ α, nab y ((N : ℤ) ^ 2) (F2 q i b) α = r * nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) α := by
      intro b
      obtain ⟨j, hj1, hj2⟩ := hkill b
      have hW1 := h58.2 (tp1 q b) (u b) j (ht2 b) (hsq _ (hu1 b)) hj1 hj2
      have hA : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp1 q b * u b) (F2 q i b) := by
        rw [← htp b]
        exact hF2 q i b
      have hB : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (u b * z2 i b) (tp1 q b) (F1 q (ρ i) b) := by
        have h1 := hF1 q (ρ i) b
        rw [hρ i] at h1
        exact h1
      obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.T.thetaGroup_shift_halfTorsion_root hL E H Dw l Xo T y.x N hNodd y.s (tp1 q b) (u b) (z2 i b)
        (e b) (ht2 b) (hsq _ (hu1 b)) ((hz2 i).1 b) hW1 (he b) _ _ hA hB
      exact ⟨r, hr1, hr2, GlobalTheory.T.connection_linear_in_section E H Dw l Xo c nab hnab T y N _ _ r hr3⟩
    choose r hr using hr
    have hprod : ∏ b, r b = 1 := by
      apply eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one _ N hNodd
      · apply shortSum_toΓ_injective T
        rw [map_one, map_pow, map_prod, ← Finset.prod_pow,
          Finset.prod_congr rfl (fun b _ => (hr b).1), ← Units.coe_prod, hpe, Units.val_one]
      · rw [← Finset.prod_pow]
        exact Finset.prod_eq_one (fun b _ => (hr b).2.1)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    rw [Finset.prod_congr rfl (fun b _ => (hr b).2.2 (colOf m b)), Finset.prod_mul_distrib, hprod, _root_.one_mul]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  exact (hρbij.sum_comp (fun j => ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
    ∏ b, nab y ((N : ℤ) ^ 2) (F1 q j b) (colOf m b))).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MarginsOfGaps
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem margins_of_gaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X), 0 < X.p0 → X.p0 < r → Nonempty X.Ψ → Xa.de = de2W X → IsStrictDom X Xa.L → (∀ τ (a b : Fin r), a ≤ b → ((b : ℕ) < X.p0 ∨ X.p0 ≤ (a : ℕ)) → (Xa.Fp - kapW X - nd X • Xa.L) τ b ≤ (Xa.Fp - kapW X - nd X • Xa.L) τ a) → ∀ bb m mL : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → (∀ τ (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → m ≤ (((Xa.Fp - kapW X - nd X • Xa.L) τ b : ℤ) : ℝ) - (((Xa.Fp - kapW X - nd X • Xa.L) τ a : ℤ) : ℝ) ∧ mL ≤ ((Xa.L τ b : ℤ) : ℝ) - ((Xa.L τ a : ℤ) : ℝ)) → bb + 2 * Xa.T < m → bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m + nd X * mL → 2 * (r : ℝ) < m → Margins X Xa := by
  intro E _ _ _ r X Xa h0 hr _ hde hL hgap bb m mL hbb hpair hm1 hm2 _
  obtain ⟨g1, g2, g3, g4⟩ := GlobalTheory.ThetaRecordCompare.arch_gaps Xa h0 hr
  have hT : (0 : ℝ) ≤ Xa.T := Nat.cast_nonneg _
  have hde2 : GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X Xa.de := by
    rw [hde]
    intro τ i j
    refine ⟨fun h => ?_, fun a b => ?_⟩
    · simp only [de2W]
      split_ifs <;> omega
    · simp only [de2W]
      split_ifs <;> omega
  have hA : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ := fun x0 ho z hz ξ => by
    rw [← IW.leviM_comb X x0 ho hz]
    exact (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ m
      (fun τ i j a b => hgap τ i j a (Or.inl b)) (fun τ i j a b => hgap τ i j b (Or.inr a))
      (fun τ i j a b => (hpair τ i j a b).1) x0 ho z hz ξ
  have hB : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      mL * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.L) z ξ :=
    (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ mL
      (fun τ i j a b => by
        rcases a.eq_or_lt with h | h
        · rw [h]
        · exact ((hL τ).1 i j h b).le)
      (fun τ i j a b => by
        rcases b.eq_or_lt with h | h
        · rw [h]
        · exact ((hL τ).2.1 i j a h).le)
      (fun τ i j a b => (hpair τ i j a b).2)
  refine ⟨⟨bb, m - 2 * Xa.T, hbb, by linarith, fun t ht x0 ho z hz ξ => ?_⟩,
    ⟨bb, m + nd X * mL, hbb, hm2, fun x0 ho z hz ξ => ?_⟩, fun x0 ho z hz ξ => ?_,
    (GlobalTheory.ThetaRecordCompare.arch_extra Xa).2.2.2.1,
    fun k P => GlobalTheory.ThetaRecordCompare.cusp_of_gaps Xa.n_ge h0 hr
      (GlobalTheory.ThetaRecordCompare.gaps_add g3 (GlobalTheory.ThetaRecordCompare.gapsGe_mono g1 zero_le_one) k)
      (GlobalTheory.ThetaRecordCompare.pair_add g4 g2 k)⟩
  · have a := hA x0 ho z hz ξ
    have hrh := GlobalTheory.ThetaRecordCompare.leviRh_nonneg X ho hz ξ
    rcases ht with rfl | ht
    · have := mul_nonneg hT hrh
      nlinarith
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      have b := Xa.base_psi_levi_lower_bound x0 (IW.orth_mem_dom X x0 ho) z hz ξ
      have c : leviM X (phla X Xa.de) x0 z ξ = 2 * leviRh X x0 z ξ :=
        GlobalTheory.ThetaRecordCompare.levi_twoDelta hde2 ho hz ξ
      have ht : 0 ≤ 1 + Xa.c1 / Xa.a1 := by have := Xa.frame_theta_const_pos; have := Xa.frame_theta_weight_pos; positivity
      have d := mul_le_mul_of_nonneg_left b ht
      have e := mul_le_mul_of_nonneg_right Xa.rr_le hrh
      rw [c] at d
      unfold leviO at *
      nlinarith
  · have a := hA x0 ho z hz ξ
    have b := mul_le_mul_of_nonneg_left (hB x0 ho z hz ξ) (Nat.cast_nonneg (α := ℝ) (nd X))
    nlinarith
  · by_cases hξ : ξ = 0
    · subst hξ; simp [leviO, leviM, leviV]
    · exact (Xa.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le

end GlobalTheory.Shares
end

