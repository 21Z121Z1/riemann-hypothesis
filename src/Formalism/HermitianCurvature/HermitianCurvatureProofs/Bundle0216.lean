import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0071
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0137
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0073
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0134

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtMinusW
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem onOld_id {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {w : List C.Letter} :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
      KB.onOld (⇑(LinearMap.id : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] _)) ys x = x
  | [], x => rfl
  | y :: ys, x => by
    funext e
    simp only [KB.onOld]
    rw [onOld_id ys]
    exact congrArg x (Fin.cons_self_tail e)

theorem mix_push {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) {K d : ℕ}
    (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) (p q : C.LPt) :
    KB.mix S v ε i (PBD.pushU grid mk) (PBD.pushTh grid mk) p q =
      ∑ n : Fin K → Fin (d + 1), (F7.thGrid grid n : ℂ) *
        KB.gN S v ε i (mk (List.ofFn fun b => grid b (n b))) p q := by
  unfold KB.mix PBD.pushTh
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmem : mk (List.ofFn fun b => grid b (n b)) ∈ PBD.pushU grid mk :=
    Finset.mem_image_of_mem _ (Finset.mem_univ n)
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    simp

section sizes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem sizeAt_plusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.plusW ys a) = (ys.map fun y => |S.P v y|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.plusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_minusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.minusW ys a) = (ys.map fun y => |S.P v (y + 1)|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.minusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_pos (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : D.AdmAt S v a) : 0 < S.sizeAt v a := by
  obtain ⟨w, hw⟩ := ha
  have hA := (PBD.admissible_list_of_word S w v).1
  rw [hw] at hA
  unfold C.HidaSetting.sizeAt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hnode := hA j hj
  have hgrid : (∃ a', PBD.nodeOf a[j] ∈ S.grid v a') ∨ PBD.nodeOf a[j] ∈ S.grid1 v := by
    rcases Finset.mem_union.1 hnode with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr h
  obtain ⟨-, -, hP, hP1⟩ := (hG v).2.2.2.2.2 _ hgrid
  refine abs_pos.2 ?_
  unfold PBD.nodeOf at hP hP1
  split_ifs at hP hP1 with hs
  · exact hP
  · simpa using hP1

end sizes

section nodes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def NodeOK (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (one : Bool) (y : ℝ) : Prop :=
  (one = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ y ∈ S.grid v a') ∨
    (one = true ∧ y ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, y) x)

theorem nodes_level (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a)
    (K : ℕ) (hK : a.length + K ≤ S.Ntop) (j : ℕ) (hj : j ≤ S.G.r) :
    ∃ grid : Fin K → Fin (2 * j + 1) → ℝ,
      (∀ b, Function.Injective (grid b)) ∧
      (∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * j)) ∧
      (∀ n : Fin K → Fin (2 * j + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        (List.ofFn fun b => grid b (n b)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun b => grid b (n b)), NodeOK S v a (decide (j = 0)) y) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.minusW ys a)
        (PBD.pushTh grid fun ys => KB.minusW ys a) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := PBCut.cutInside_of_built hB
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  ·
    obtain ⟨ys, hlen, -, hg1, hp, hm, hcp, hcm, hpw⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible_level_one E Wp Wq S hGo hGr hCI v a K ha hK
    set grid : Fin K → Fin (2 * 0 + 1) → ℝ := fun b _ => ys.get ⟨b, by rw [hlen]; exact b.2⟩ with hgrid
    have hys : ∀ n : Fin K → Fin (2 * 0 + 1), (List.ofFn fun b => grid b (n b)) = ys := by
      intro n
      apply List.ext_get
      · simp [hlen]
      · intro i h1 h2
        simp [hgrid]
    have hsep : ∀ y ∈ ys, ∀ x ∈ a, PBD.Sep (true, y) x := by
      obtain ⟨w, hw⟩ := hp
      have hA := (PBD.admissible_list_of_word S w v).2
      rw [hw, PBD.plusW_eq] at hA
      intro y hy x hx
      exact (List.pairwise_append.1 hA).2.2 _ (List.mem_map.2 ⟨y, hy, rfl⟩) _ hx
    have hmk : ∀ mk : List ℝ → List C.Letter, (mk ys = KB.plusW ys a ∨ mk ys = KB.minusW ys a) →
        ∀ n : Fin K → Fin (2 * 0 + 1), D.AdmAt S v (mk (List.ofFn fun b => grid b (n b))) ∧
          (mk (List.ofFn fun b => grid b (n b))).length ≤ a.length + K := by
      intro mk hmk n
      rw [hys n]
      rcases hmk with h | h <;> rw [h]
      · exact ⟨hp, by rw [PBD.plusW_eq]; simp [hlen]; omega⟩
      · exact ⟨hm, by rw [PBD.minusW_eq]; simp [hlen]; omega⟩
    refine ⟨grid, fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega), fun b => ?_, fun n => ?_, ?_, ?_⟩
    · simp [F7.lagCo]
    · rw [hys n]
      refine ⟨hp, hm, hcp, hcm, hpw.imp fun h => by linarith, fun y hy => Or.inr ⟨rfl, hg1 y hy, hsep y hy⟩⟩
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.plusW ys a) (Or.inl rfl))
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.minusW ys a) (Or.inr rfl))
  ·
    obtain ⟨-, grid, hinj, hl1, hmem, hall, hlp, hlm⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a K (2 * j) ha hK (by omega)
    refine ⟨grid, hinj, hl1, fun n => ?_, hlp, hlm⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall n
    refine ⟨h1, h2, h3, h4, h5.imp fun h => by linarith, fun y hy => Or.inl ⟨by simp; omega, ?_⟩⟩
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨a.length + K - b, by omega, by omega, hmem b (n b)⟩

end nodes

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem hsInner_zero_left' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) A = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) => (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
    simp; rfl
  rw [this, inner_zero_right]

section vec

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_zero_small (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    {G : B.Mat k r → (Wq →L[ℂ] Wp)} {ε : ℝ} (hG : ∀ g ∈ B.GV k r, G g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g)
    (q : C.LPt) (hq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q < ε) : D.vecV Bs ν' m₀ G q = 0 := by
  unfold D.vecV
  by_cases hq' : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos hq']
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose hq'.1 h'.choose_spec.2.1
      have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq'.1.2 ▸ D.ptPerm q)) G (fun _ => 0) 0 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
        have hz : G (B.sgs p h'.choose) = 0 := by
          by_contra hne
          have h1 := hG _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) hne
          rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, ← hGq] at h1
          linarith
        simp [D.orbIntegrand, B.rho, hz])
      rw [e, zero_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq']

end vec

theorem rr_top_small {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (Cb : ℝ) (hθ : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hw : KB.CutWord P p.l0 w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℂ, Complex.normSq c - P.T * P.T' < δ →
      p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
  classical

  have hθc := fun e => Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hθ hF hw
  choose F' hF'c hF'd hF'v using hθc
  obtain ⟨εF, hεF, hGF⟩ := hF.2.2
  choose εe hεe hGe using fun e => (hF'c e).2.2
  let Sε : Finset ℝ := insert εF (Finset.univ.image εe)
  have hne : Sε.Nonempty := ⟨εF, Finset.mem_insert_self _ _⟩
  set ε := Sε.min' hne with hεdef
  have hε : 0 < ε := by
    rw [hεdef, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hεF
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact hεe a
  have hεF' : ε ≤ εF := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hεe' : ∀ e, ε ≤ εe e := fun e =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ e)))
  set Dh := Complex.normSq (D.ptMatN h P.r).det with hDh
  have hD0 : 0 ≤ Dh := Complex.normSq_nonneg _
  have hD1 : 0 < Dh + 1 := by linarith
  refine ⟨ε / (Dh + 1), div_pos hε hD1, fun c hc => ?_⟩
  have hTT : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' = P.T * P.T' := by
    rw [p.hP.2.2.2.1, p.hP.2.2.2.2.1]
  have hpt : D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (h ++ [(1, c)]) < ε := by
    rw [hTT, Formalism.FourierDecayAlt.P.PBD.ptG_app _ c h P.r hh.2]
    by_cases hs : Complex.normSq c - P.T * P.T' ≤ 0
    · have : Dh * (Complex.normSq c - P.T * P.T') ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD0 hs
      linarith
    · push Not at hs
      have h1 : Dh * (Complex.normSq c - P.T * P.T') ≤ (Dh + 1) * (Complex.normSq c - P.T * P.T') := by nlinarith
      have h2 : (Dh + 1) * (Complex.normSq c - P.T * P.T') < (Dh + 1) * (ε / (Dh + 1)) :=
        mul_lt_mul_of_pos_left hc hD1
      rw [mul_div_cancel₀ _ hD1.ne'] at h2
      linarith
  unfold KB.Pl.RR D.RRplace
  split_ifs with hloc hi hi2 hw0
  · omega
  · have hv : D.vecV p.T.base p.ν' p.m₀ F (h ++ [(1, c)]) = 0 :=
      vecV_zero_small p.T.base p.ν' p.m₀ (fun g hg h0 => le_trans hεF' (hGF g hg h0)) _ hpt
    rw [hv, hsInner_zero_left']
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    have hv : D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (h ++ [(1, c)]) = 0 := by
      have := hF'v e (h ++ [(1, c)])
      unfold KB.Pl.V at this
      rw [this]
      exact vecV_zero_small p.T.base p.ν' p.m₀ (fun g hg h0 => le_trans (hεe' e) (hGe e g hg h0)) _ hpt
    rw [hv, ContinuousLinearMap.comp_zero, hsInner_zero_left', mul_zero]
  · omega
  · rfl

section law

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem zetaNorm_map {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ) :
    μ.map (fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) =
      (volume : Measure ℂ).withDensity (Formalism.FourierDecayAlt.P.JCx2.rbW k (Tz k r Bs.z) (Tz k r Bs.z')) := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  refine Measure.ext_of_lintegral _ fun ψ hψ => ?_
  rw [lintegral_map hψ hf, hμ.2 ψ hψ, lintegral_withDensity_eq_lintegral_mul _ (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _) hψ]
  rfl

theorem zetaNorm_integral {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ)
    (ψ : ℂ → ℂ) (hψ : Measurable ψ) :
    ∫ g, ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) ∂μ =
      ∫ ζ, (B2.zWeight k (Tz k r Bs.z) (Tz k r Bs.z') ζ : ℂ) * ψ ζ := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  rw [← integral_map hf.aemeasurable hψ.aestronglyMeasurable, zetaNorm_map hμ,
    integral_withDensity_eq_integral_toReal_smul (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _)
      (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Formalism.FourierDecayAlt.P.JCx2.rbW]
  rw [ENNReal.toReal_ofReal (Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]

theorem zetaNorm_integrable {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ)
    (ψ : ℂ → ℂ) (hψ : Measurable ψ)
    (hi : Integrable (fun g => ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g))) μ) :
    Integrable (fun ζ => (B2.zWeight k (Tz k r Bs.z) (Tz k r Bs.z') ζ : ℂ) * ψ ζ) := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  have h1 : Integrable ψ (μ.map fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) :=
    (integrable_map_measure hψ.aestronglyMeasurable hf.aemeasurable).2 hi
  rw [zetaNorm_map hμ, integrable_withDensity_iff_integrable_smul' (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _)
    (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)] at h1
  refine h1.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Formalism.FourierDecayAlt.P.JCx2.rbW]
  rw [ENNReal.toReal_ofReal (Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]

end law

section pic

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pic_cpt {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (K0 : Submodule ℂ (RadSp k r Bs.z Bs.z' Bs.π Bs.π'))
    (hJ : ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
      HasCompactSupport F → (∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g) →
      ∃ Φ ∈ K0, ∀ x ∈ DomR k r Bs.z Bs.z',
        (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (B.JF Bs F) x.1 x.2)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    ∃ Φ ∈ K0, ∀ x ∈ DomR k r Bs.z Bs.z',
      (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (B.JF Bs F) x.1 x.2 := by
  classical
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  set F₂ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => if g ∈ B.GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ B.GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hs₂ : B.CkOn ⊤ (B.GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hs g₀ hg₀
    exact ⟨U, f', hU, hgU, hf', fun g hg hgG => by rw [he g hgG, hfe g hg hgG]⟩
  have hz : ∀ g, g ∉ {g : B.Mat k r | B.gN g ≤ R} → F₂ g = 0 := by
    intro g hg
    by_cases hgG : g ∈ B.GV k r
    · rw [he g hgG]
      by_contra h0
      exact hg (hR g hgG h0)
    · simp [hF₂, hgG]
  have hC := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R
  obtain ⟨Φ, hΦK, hΦ⟩ := hJ F₂ ε hε
    (fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hs₂ hC (fun g _ hgC => hz g hgC) A m)
    (HasCompactSupport.intro hC hz)
    (fun g hg h0 => hG g hg (by rwa [he g hg] at h0))
  refine ⟨Φ, hΦK, fun x hx => ?_⟩
  rw [hΦ x hx]
  have hGV : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by
    rw [Rad.wCell_last_eq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hx.1 (by simp)) hx.2.1.1
  simp only [resG]
  rw [Formalism.FourierDecayAlt.P.Qx8.JF_congr Bs (a := 1) (fun g hg => by rw [he g hg, one_smul]) hGV, one_smul]

end pic

def TopContOn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (hh' : D.IsLocPt h' P.r) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F →
    KB.CutWord P p.l0 w →
    ContinuousOn (fun c : ℂ => p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]))
      {c : ℂ | P.T * P.T' < Complex.normSq c}

end Formalism.FourierDecayAlt.P.PBO
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def topR {P : M.Par} (l0 : ℕ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty P) (y : ℝ) : ℂ :=
  Wd.qw (M.qC P) (D.positionted w) (y : ℂ) / Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) e ((y : ℂ) + 1)

def TopRatio : Prop :=
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → 28 * Real.exp 1 ≤ Cc → ∀ (v : Fin S.f) (w : List C.Letter) (y : ℝ),
    KB.CutWord (D.parOf S v) (S.l + 1) ((true, y) :: w) → (∃ m, y ∈ S.grid v m) → w.length < S.Ntop →
    (∀ x ∈ w, (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - x.2| ∧ (x.1 = false → (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - (x.2 - 1)|)) →
    ∀ (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)),
      0 < (topR (S.l + 1) w e ρ y).re ∧ (topR (S.l + 1) w e ρ y).im = 0 ∧
      |S.P v y| ≤ Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (Real.sqrt (S.T * S.T'))⁻¹ * (topR (S.l + 1) w e ρ y).re

def lamTop {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (b : ℕ) (v : Fin S.f) : ℝ :=
  √((2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r b ((S.G.r : ℤ) + 2 - b))) * Real.exp 1 *
    (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
    (√(S.T * S.T'))⁻¹)

def TopLocB : Prop :=
  KB.DegTop → Top.VecVTypes → TopRatio →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    (∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ v, 0 ≤ lamTop S (S.G.r + 2 - s) v ∧
      2 * lamTop S (S.G.r + 2 - s) v ≤ S.base.szL (S.G.r + 2 - s) s v) ∧
    ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.TopLoc (setC S p F) v fun b _ => lamTop S b v

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralPositive
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

theorem top_unipotent_integral_positive (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r))
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) (hR : 1 ≤ P.r) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have h0 := p.hT 0 (Nat.zero_le _)
  have hr := p.hT P.r le_rfl
  exact vecV_append_singleton_eq_vecV_sliceAt P.k P.r (P.r - P.r) (Nat.sub_self _) (by omega) p.T.base (p.T.bs P.r)
    (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) (p.T.π_lev P.r le_rfl) (p.T.π'_lev P.r le_rfl)
    h0.2.2 h0.1 h0.2.1 hr.1 hr.2.1 hr.2.2 p.ν' p.m₀ ν'r m₀r hν hm p.hF
    (CompactCoefficientAppend.baseFrame_last p ν'r m₀r hν hm) h hh ζ hζ F hF hR _

theorem highestUnipotentIntegral : PBI.HighestUnipotentIntegral := by
  intro Wp Wq _ _ _ _ _ _ P p F h ζ hh ν'r m₀r hF hζ hν hm
  by_cases hR : P.r = 0
  · exact CompactCoefficientAppend.top_unipotent_integral_zero Wp Wq P p F h ζ hh ν'r m₀r hR hF hζ hν hm
  · exact top_unipotent_integral_positive Wp Wq P p F h ζ hh ν'r m₀r hF hζ hν hm (by omega)

end Formalism.FourierDecayAlt.P.PBM

namespace Formalism.FourierDecayAlt.P

theorem top_unipotent_integral : PBI.HighestUnipotentIntegral := PBM.highestUnipotentIntegral

end Formalism.FourierDecayAlt.P
end
end

