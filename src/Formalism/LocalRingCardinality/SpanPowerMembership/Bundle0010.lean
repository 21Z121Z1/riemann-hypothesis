import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0006
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0008
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0009
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowC

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.EntPlNonempty
section
open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

def zeroEnt (D : D7) (Dx : DivX D) (Tw : TwForms D)
    (lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w])
    (h1 : ∀ w x, iL w x = lamV (lam w) (D.what₂.embLL x))
    (h2 : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1)
    (h0 : ∀ u μ i, Subsingleton ((Tw.fm u μ).lat i).V) : KerEnt D Dx Tw where
  lam := lam
  iL := iL
  iL_lam := h1
  iL_int := h2
  Th := fun _ _ _ _ _ _ => 0
  VQ := fun _ _ _ _ => PUnit
  ev := fun _ _ _ _ => 0
  ev_inj := fun _ _ _ _ a b _ => Subsingleton.elim a b
  prS := fun _ _ _ _ _ => 0
  prT := fun _ _ _ _ _ => 0
  prT_val := fun _ _ _ _ _ _ _ _ _ => ⟨0, by simp⟩
  lat_S := by
    intro u μ w _ i _ φ
    have := h0 u μ i
    constructor
    · rintro ⟨x, _, rfl⟩
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, fun c => ⟨PUnit.unit, by simp, by simp⟩⟩
    · rintro ⟨_, h⟩
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero]
      funext c
      obtain ⟨v, hv, _⟩ := h c
      simpa using hv
  levelFree_lattice_condition := by
    intro u μ w _ i _ φ
    have := h0 u μ (i + 1)
    constructor
    · rintro ⟨x, _, rfl⟩
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, fun c => ⟨PUnit.unit, by simp, by simp⟩⟩
    · rintro ⟨_, h⟩
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero]
      funext c
      obtain ⟨v, hv, _⟩ := h c
      simpa using hv
  un := fun _ _ _ _ _ _ => 1
  un_ne := by intros; exact one_ne_zero
  kform := by intros; simp

structure EntPl (D : D7) where
  lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]
  iL_lam : ∀ w x, iL w x = lamV (lam w) (D.what₂.embLL x)
  iL_lam' : ∀ w x (hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ), iL w x = lam w ⟨D.what₂.embLL x, hx⟩
  iL_int : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1

theorem entPl_nonempty (D : D7) : Nonempty (EntPl D) := by
  choose lam iL h1 h2 using fun w => exists_placeEmb D w
  exact ⟨⟨lam, iL, fun w x => by
    obtain ⟨hx, e⟩ := h1 w x
    rw [lamV, dif_pos hx, e], fun w x _ => (h1 w x).choose_spec, h2⟩⟩

def entZero (D : D7) (Dx : DivX D) (Tw : TwForms D) (P : EntPl D)
    (h0 : ∀ u μ i, Subsingleton ((Tw.fm u μ).lat i).V) : KerEnt D Dx Tw :=
  zeroEnt D Dx Tw P.lam P.iL P.iL_lam P.iL_int h0

theorem entZero_lam (D : D7) (Dx Tw P h0) : (entZero D Dx Tw P h0).lam = P.lam := rfl

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NStageTrivialCharacterCoeffEq
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.MainNotions.S

theorem not_cover_of_isEmpty (D : D7) (h : IsEmpty D.ntw.Tw) : ¬ NTw.TwCover D.ntw := by
  intro hT
  have h2 : Ideal.span {((2 : ℕ) : 𝓞 ↥D.LL0)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    exact top_primitive (K := ↥D.LL0) 2 one_lt_two (by rw [Ideal.span_singleton_eq_top.mpr hu])
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h2
  have hm : ((2 : ℕ) : 𝓞 ↥D.LL0) ∈ P := hle (Ideal.mem_span_singleton_self _)
  have hne : P ≠ ⊥ := by
    rintro rfl
    exact two_ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hm))
  obtain ⟨i, -⟩ := hT 2 Nat.prime_two ⟨P, hP.isPrime, hne⟩ hm
  exact h.false i

structure TwGap (D : D7) where
  ntw : NTw D.R D.host D.what₂ D.LL0 D.nd
  nexp : NExp D.R D.host D.what₂ D.LL0 D.nd ntw
  nth : NTh D.R D.host D.what₂ D.LL0 D.nd ntw nexp
  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E (ntw.l i) →
    LocBridge (ntw.l i) D.host.E D.nd.Om (ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)) (ntw.O0 i)

  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (ntw.l i))
    (x : D.nd.Om), x ∈ D.nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g D.nd, D.what₂.embLL ((nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g
  cover : NTw.TwCover ntw

def withTw (D : D7) (W : TwGap D) : D7 :=
  { D with ntw := W.ntw, nexp := W.nexp, nth := W.nth, ntwbr := W.ntwbr, ntwbr_ind := W.ntwbr_ind, nStage_trivialCharacter_coeff_eq := W.nStage_trivialCharacter_coeff_eq }

theorem galTop (D : D7) (h : D.LL0 = ⊤) : IsGalois ℚ ↥D.LL0 :=
  h ▸ IsGalois.of_algEquiv (IntermediateField.topEquiv (F := ℚ) (E := D.what₂.LL)).symm

theorem ties_withTw (D : D7) (W : TwGap D) (hcd : D.s.cdScale = CD.cdScaleOf D.cd) (hds : dsigTie D)
    (hper : ∀ u μ φ F, D.what₂.perCol u μ φ F = 0) (hB : ∀ u φ F, D.what₂.Bu u φ F = 0)
    (hFT : IsEmpty D.what₂.FT)
    (hgal : IsGalois ℚ ↥D.LL0 := by exact Formalism.BasicNotions.Examples₂.galTop _ rfl) :
    Ties (withTw D W) where
  cdScale_tie := fun n ε P Q e h1 h2 A hA => by
    show ((D.s.cdScale n ε : ENNReal) • Formalism.REAL.muG ε) A = D.cd.cd P Q _
    rw [hcd]
    exact CD.cdScaleOf_tie D.cd n ε P Q e h1 h2 A hA
  dsig_tie := hds
  bu_def := by
    intro u φ F
    exact (hB u φ _).trans (hper u _ φ _).symm
  tw_cover := twCoverPair_of (NTw.levelLetterCocycles_of_fact _ W.cover)
  ft_occ := fun σ => hFT.elim σ
  baseField_isGalois := hgal

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZRowD
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

variable (D : D7)

def divXStd (n : ℕ → ℕ) (bM : ∀ j, OrthonormalBasis (Fin (n j)) ℂ (D.what₂.Mj j))
    (hg : ∀ j, (D.what₂.MjLat j).gen = genB (bM j)) (kap : ℝ) (hk : 0 < kap) : DivX D where
  geo := geoExample _
  Lev := Empty
  levPr := fun κ => κ.elim
  shv := fun _ κ => κ.elim
  shv_N := fun _ κ => κ.elim
  shv_lev := fun _ κ => κ.elim
  PlP := fun p _ => {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}
  plpFin := fun p _ => PlOver.plFin D p
  plpNe := fun p _ => PlOver.plNe D p
  wtP := fun p _ la => PlOver.wt D p la.1
  divisorWeight_nonneg := fun p _ la => PlOver.wt_nonneg D p la.1
  divisorWeight_sum := fun p _ => PlOver.wt_sum D p
  plP := fun _ _ => Equiv.refl _
  divisorWeight_def := fun _ _ _ => rfl
  jC := fun p _ _ => (teich_Om_equiv p).some.toRingHom.comp (algebraMap (DV.KW p) (TeichOm p))
  Mp := fun _ κ => κ.elim
  md := fun _ κ => κ.elim
  vdd := fun _ _ => 0
  vdd_unram := fun _ _ _ => rfl
  vdd_nonneg := fun _ _ => le_rfl
  CurveM := fun _ κ => κ.elim
  degM := fun _ κ => κ.elim
  htMdl := fun _ κ => κ.elim
  htCurve := fun _ κ => κ.elim
  htCurve_deg := fun _ κ => κ.elim
  MjH := fun j => stdH D.what₂.LL (n j)
  MjH_good := fun j => stdH_good _ _
  jM := fun j => jB D.what₂.embLL (bM j)
  jM_basis := fun j => jB_basis _ _
  jM_lat := fun j _ _ x => by rw [hg]; exact jB_lat _ _ x
  jM_metric := fun j _ _ x => jB_norm _ _ x
  Qp := fun _ => ∅
  degreeZero_partial_set_empty := rfl
  Qp_muAt := fun _ => Finset.notMem_empty _
  Qp_g := fun _ _ _ => Finset.notMem_empty _
  QPl := fun _ => Empty
  qv := fun _ v => v.elim
  qv_gt := fun _ v => v.elim
  qv_char := fun _ _ v => v.elim
  nu := fun _ v => v.elim
  nu_ne := fun _ v => v.elim
  nu_abs := fun _ v => v.elim
  ZQ := fun _ v => v.elim
  quotientLocalValueFirst := fun _ v => v.elim
  typeDim := fun _ v => v.elim
  Comp := fun _ => Empty
  degHH := fun _ c => c.elim
  Yv := fun _ c => c.elim
  Ybd := fun _ c => c.elim
  Lw := fun _ c => c.elim
  iMj := fun _ c => c.elim
  iMj_mem := fun _ c => c.elim
  logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
  logLam_base := fun _ _ => rfl
  kapR := fun _ => kap
  kapR_pos := fun _ => hk
  kapR_conj := fun _ => rfl
  MjLat_sub := fun j _ _ => by rw [hg]; exact jB_gen _ _
  phiFr_unram := fun _ κ => κ.elim
  Surf := Empty
  surfCh2 := fun _ => 0
  surfDegOm := fun _ => 0
  SurfFp := Empty
  surfFpCh2 := fun _ => 0

theorem ijIdx_zero {D : D7} (X : DivX D) (μ j w) (h : (X.MjH j).L = Idx.thTj X μ j) : Idx.IjIdx X μ j w = 0 := by
  unfold Idx.IjIdx Formalism.HermitianLatticesTheory.lidx
  rw [h]; exact sub_self _

theorem jwIdx_zero (μ j w) (h : Idx.TjL D μ j = Idx.TjDual D μ j) : Idx.jwIdx D μ j w = 0 := by
  unfold Idx.jwIdx Formalism.HermitianLatticesTheory.lidx
  rw [← h]; exact sub_self _

theorem lamDef_of (h : ∀ μ j π, ∀ x ∈ D.what₂.isot j π,
    D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = ((D.what₂.lamP μ j π : ℝ) : ℂ) • x) : DV.LamDef D :=
  fun μ j _ _ π h0 => (DV.lamTr_of_scalar D μ j π _ h0 (h μ j π)).symm

section Kap

variable {D} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

theorem iiStar_id (he : S.eOp D.what₂.mu0 = LinearMap.id)
    (hiso : ∀ x y, inner ℂ (S.iota D.what₂.mu0 x) (S.iota D.what₂.mu0 y) = inner ℂ x y)
    (hs : Function.Surjective (S.iota D.what₂.mu0)) : S.iiStar = LinearMap.id := by
  have hi : Function.Injective (S.iota D.what₂.mu0) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have := hiso x x
    rw [LinearMap.mem_ker.mp hx, inner_zero_left] at this
    exact inner_self_eq_zero.mp this.symm
  ext x
  refine ext_inner_right ℂ fun y => ?_
  obtain ⟨z, rfl⟩ := hs y
  have hz : z ∈ S.Qsp D.what₂.mu0 := by rw [Qsp_top S he hi]; trivial
  show inner ℂ (S.iota D.what₂.mu0 (LinearMap.adjoint (S.iotaQ D.what₂.mu0) x : S.Amb D.what₂.mu0))
    (S.iota D.what₂.mu0 z) = inner ℂ x (S.iota D.what₂.mu0 z)
  rw [hiso]
  have h1 : inner ℂ (LinearMap.adjoint (S.iotaQ D.what₂.mu0) x) (⟨z, hz⟩ : S.Qsp D.what₂.mu0) =
      inner ℂ x (S.iotaQ D.what₂.mu0 ⟨z, hz⟩) := LinearMap.adjoint_inner_left _ _ _
  exact h1

theorem kapOf_one {n : ℕ} (ty : Fin n → D.what₂.FT) (hii : S.iiStar = LinearMap.id)
    (hl : ∀ j π, D.what₂.lamP D.what₂.mu0 j π = 1) : S.kapOf ty = 1 := by
  have hr : S.kapRatio ty = 1 := by
    unfold RowSide.kapRatio DV.lamProd
    rw [hii, LinearMap.det_id]
    simp [hl]
  unfold RowSide.kapOf
  rw [hr, if_pos one_pos, Real.one_rpow]

end Kap

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZRowV
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions MvPolynomial

section Det

theorem det_ind {p N : ℕ} (I : Fin p ↪o Fin N) {C : Type} [CommRing C] :
    (Matrix.of fun i k : Fin p => if (i : ℕ) = (I k : ℕ) then (1 : C) else 0).det =
      if ∀ k, (I k : ℕ) = k then 1 else 0 := by
  split_ifs with h
  · have : (Matrix.of fun i k : Fin p => if (i : ℕ) = (I k : ℕ) then (1 : C) else 0) = 1 := by
      ext i k
      simp only [Matrix.of_apply, Matrix.one_apply, h k, Fin.val_inj]
    rw [this, Matrix.det_one]
  · push Not at h
    obtain ⟨k, hk⟩ := h
    have hge : ∀ j : Fin p, (j : ℕ) ≤ (I j : ℕ) := fun j => by
      have := StrictMono.id_le (f := fun n : ℕ => if hn : n < p then (I ⟨n, hn⟩ : ℕ) + 0 else n + N) (by
        intro a b hab
        by_cases hb : b < p
        · have ha : a < p := lt_trans hab hb
          simp only [dif_pos ha, dif_pos hb, add_zero]
          exact I.strictMono (show (⟨a, ha⟩ : Fin p) < ⟨b, hb⟩ from hab)
        · simp only [dif_neg hb]
          by_cases ha : a < p
          · simp only [dif_pos ha, add_zero]
            have := (I ⟨a, ha⟩).2
            omega
          · simp only [dif_neg ha]; omega) j
      simpa [j.2] using this
    have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) k.2
    let last : Fin p := ⟨p - 1, by omega⟩
    have hlast : p ≤ (I last : ℕ) := by
      have h1 : (k : ℕ) < (I k : ℕ) := lt_of_le_of_ne (hge k) (Ne.symm hk)
      have h2 : ∀ n : ℕ, ∀ hn : (k : ℕ) + n < p, (I k : ℕ) + n ≤ (I ⟨k + n, hn⟩ : ℕ) := by
        intro n
        induction n with
        | zero => intro hn; simp
        | succ n ih =>
          intro hn
          have h3 := ih (by omega)
          have hlt : (I ⟨k + n, by omega⟩ : ℕ) < (I ⟨k + (n + 1), hn⟩ : ℕ) :=
            I.strictMono (show (⟨k + n, by omega⟩ : Fin p) < ⟨k + (n + 1), hn⟩ from by
              rw [Fin.lt_iff_val_lt_val]; simp)
          omega
      have h4 := h2 (p - 1 - k) (by omega)
      have e : (⟨k + (p - 1 - k), by omega⟩ : Fin p) = last := Fin.ext (by simp [last]; omega)
      rw [e] at h4
      omega
    refine Matrix.det_eq_zero_of_column_eq_zero last fun i => ?_
    simp only [Matrix.of_apply]
    rw [if_neg]
    have := i.2
    omega

end Det

section Eval

variable {Lt : Type} (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime]

def xS : Lt × ℕ × Fin N0 → ℂ_[l] := fun k => if k.2.1 = (k.2.2 : ℕ) then 1 else 0

def zS : Lt × Fin N0 × Fin N1 → ℂ_[l] := fun k => if (k.2.1 : ℕ) = (k.2.2 : ℕ) then 1 else 0

open Classical in

def ThE : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l] := fun μ =>
  if ∀ k ∈ μ.support, zS N0 N1 l k = 1 then (μ.prod fun _ n => (n.factorial : ℂ_[l]))⁻¹ else 0

open Classical in
theorem prod_ind {σ : Type} (t : σ → ℂ_[l]) (ht : ∀ k, t k = 0 ∨ t k = 1) (μ : σ →₀ ℕ) :
    (μ.prod fun k e => t k ^ e) = if ∀ k ∈ μ.support, t k = 1 then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one fun k hk => by show t k ^ μ k = 1; rw [h k hk, one_pow]
  · push Not at h
    obtain ⟨k, hk, hne⟩ := h
    have h0 : t k = 0 := (ht k).resolve_right hne
    exact Finset.prod_eq_zero hk (by show t k ^ μ k = 0; rw [h0, zero_pow (Finsupp.mem_support_iff.mp hk)])

theorem fac_ne (μ : (Lt × Fin N0 × Fin N1) →₀ ℕ) : (μ.prod fun _ n => (n.factorial : ℂ_[l])) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

open Classical in
theorem fac_ThE (μ : (Lt × Fin N0 × Fin N1) →₀ ℕ) :
    (μ.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff μ (ThE N0 N1 l) =
      μ.prod fun k e => zS N0 N1 l k ^ e := by
  rw [prod_ind l (zS N0 N1 l) (fun k => by unfold zS; split_ifs <;> simp) μ]
  show _ * ThE N0 N1 l μ = _
  unfold ThE
  split_ifs
  · exact mul_inv_cancel₀ (fac_ne N0 N1 l μ)
  · exact mul_zero _

theorem eval_applyAt0 (P : MvPolynomial (KM.XZ Lt N0 N1) ℤ) :
    MvPolynomial.eval (xS N0 l) (KM.applyAt0 N0 N1 l (ThE N0 N1 l) P) =
      MvPolynomial.eval₂ (Int.castRingHom ℂ_[l]) (Sum.elim (xS N0 l) (zS N0 N1 l)) P := by
  unfold KM.applyAt0
  rw [map_sum, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  set e := Finsupp.sumFinsuppEquivProdFinsupp μ with he
  have hμ : μ = Finsupp.sumElim e.1 e.2 := by
    rw [he]
    ext k
    cases k <;> rfl
  have hprod : (∏ i ∈ μ.support, Sum.elim (xS N0 l) (zS N0 N1 l) i ^ μ i) =
      (e.1.prod fun k n => xS N0 l k ^ n) * (e.2.prod fun k n => zS N0 N1 l k ^ n) := by
    show μ.prod (fun i n => Sum.elim (xS N0 l) (zS N0 N1 l) i ^ n) = _
    conv_lhs => rw [hμ]
    rw [Finsupp.prod_sumElim]
    rfl
  rw [hprod, ← fac_ThE N0 N1 l e.2]
  simp only [eq_intCast, Int.cast_id]
  ring

theorem sum_xz {p : ℕ} (hp : p ≤ N0) (s : Lt) (i : Fin p) (b : Fin N1) :
    (∑ a : Fin N0, xS N0 l (s, (i : ℕ), a) * zS N0 N1 l (s, a, b)) = if (i : ℕ) = (b : ℕ) then 1 else 0 := by
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hp⟩]
  · simp [xS, zS]
  · intro a _ ha
    have : (i : ℕ) ≠ (a : ℕ) := fun h => ha (Fin.ext h.symm)
    simp [xS, this]
  · simp

variable [Fintype Lt] [DecidableEq Lt]

open Classical in
theorem eval_Gxz (nu : Lt → YoungDiagram) (hnu : ∀ s c, (nu s).colLen c ≤ N0) (I : KM.ColChoice N1 nu) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ_[l]) (Sum.elim (xS N0 l) (zS N0 N1 l)) (KM.Gxz N0 N1 nu I) =
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), if ∀ k, (I s c k : ℕ) = k then 1 else 0 := by
  unfold KM.Gxz
  rw [← MvPolynomial.coe_eval₂Hom, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold KM.minorXZ
  have hM : (MvPolynomial.eval₂Hom (Int.castRingHom ℂ_[l]) (Sum.elim (xS N0 l) (zS N0 N1 l))).mapMatrix
      (Matrix.of fun i k : Fin ((nu s).colLen c) => ∑ a : Fin N0,
        MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I s c k))) =
      Matrix.of fun i k : Fin ((nu s).colLen c) => if (i : ℕ) = (I s c k : ℕ) then (1 : ℂ_[l]) else 0 := by
    ext i k
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, map_sum]
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    exact sum_xz N0 N1 l (hnu s c) s i (I s c k)
  rw [RingHom.map_det, hM, det_ind]

open Classical in
theorem eval_nablaX (nu : Lt → YoungDiagram) (J : KM.ColChoice N0 nu) :
    MvPolynomial.eval (xS N0 l) (MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.nablaX N0 nu J)) =
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), if ∀ k, (J s c k : ℕ) = k then 1 else 0 := by
  rw [MvPolynomial.eval_map]
  unfold KM.nablaX
  rw [← MvPolynomial.coe_eval₂Hom, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, ← det_ind (C := ℂ_[l]) (J s c)]
  congr 1
  ext i k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X, xS]

end Eval

end Formalism.BasicNotions.Examples₂.NZ
end
end

