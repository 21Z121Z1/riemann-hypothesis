import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0082
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnderEqIffMapLe
section
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HeckeSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem under_eq_iff_map_le (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · rintro rfl
    exact le_rfl
  · intro h
    apply HeightOneSpectrum.ext
    exact (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top h).symm

theorem under_eq_iff (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ (Q = P ∨ Q = P') := by
  rw [under_eq_iff_map_le, h, Q.isPrime.mul_le]
  refine or_congr ⟨fun h => ?_, fun h => h ▸ le_rfl⟩ ⟨fun h => ?_, fun h => h ▸ le_rfl⟩
  · exact HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h).symm
  · exact HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h).symm

theorem not_mul_le_sq (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P') :
    ¬ P.asIdeal * P'.asIdeal ≤ P.asIdeal ^ 2 := by
  intro h
  rw [← Ideal.dvd_iff_le, sq, mul_dvd_mul_iff_left P.ne_bot, Ideal.dvd_iff_le] at h
  exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h).symm)

theorem val_eq_inv_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : Formalism.L2.Host.HChar E) (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)),
    χ.TrivOn F → χ.UnrAt P → χ.UnrAt P' → P ≠ P' →
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal → χ.val P' = (χ.val P)⁻¹ := by
  intro F E _ _ _ _ _ χ v P P' hχ h1 h2 hne hv
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hab : aboveF (L := E) F v = {P, P'} := by
    ext Q
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff v P P' hv Q
  have key : ∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v → χ.UnrAt Q →
      ¬ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal ^ 2 →
      χ.locK Q (upF F (Units.mk0 π h0)) = χ.val Q := by
    intro Q hQ hunr hu
    refine χ.val_eq hunr _ ?_
    subst hQ
    show Valued.v ((algebraMap F E π : E) : Q.adicCompletion E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', GlobalTheory.MuConj.valuation_up Q hu, hπ]
  have h := hχ.1 v (Units.mk0 π h0)
  rw [HChar.resFin_apply, hab, Finset.prod_pair hne,
    key P ((under_eq_iff v P P' hv _).2 (Or.inl rfl)) h1 (hv ▸ not_mul_le_sq P P' hne),
    key P' ((under_eq_iff v P P' hv _).2 (Or.inr rfl)) h2
      (by rw [hv, mul_comm]; exact not_mul_le_sq P' P hne.symm)] at h
  exact eq_inv_of_mul_eq_one_right h

end GlobalTheory.HeckeSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UopIsExt
section
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace LocF

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

theorem uext_mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]; exact y.2

theorem uext_ker {Λ : Submodule Lc.O (Fin n → Lc.K)} {h : GL (Fin n) Lc.K} (hh : Lc.IsFrame n h Λ)
    {V : Type*} [AddCommGroup V] [Module F V] (hV : Module.finrank F V = n) (π : (Fin n → Lc.K) → V)
    (hadd : ∀ x ∈ Λ, ∀ y ∈ Λ, π (x + y) = π x + π y)
    (hsmul : ∀ (a : Lc.O), ∀ x ∈ Λ, π (a • x) = Lc.res a • π x)
    (hsurj : ∀ y, ∃ x ∈ Λ, π x = y) {x : Fin n → Lc.K} (hx : x ∈ Λ) (h0 : π x = 0) :
    ((q : Lc.K))⁻¹ • x ∈ Λ := by
  let π' : Λ →+ V := AddMonoidHom.mk' (fun x => π x) (fun x y => hadd x x.2 y y.2)
  have hb : ∀ a : Fin n, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Pi.single a 1) ∈ Λ := by
    intro a
    rw [hh, uext_mem_std]
    intro b
    by_cases hab : b = a
    · subst hab; simp
    · simp [Pi.single_eq_of_ne hab]
  let b : Fin n → Λ := fun a => ⟨_, hb a⟩
  have key : ∀ x ∈ Λ, ∃ z : Fin n → Lc.O,
      x = Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun a => (z a : Lc.K)) ∧
      π x = ∑ a, Lc.res (z a) • π (b a) := by
    intro x hx
    have e1 : Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K)
        (Matrix.mulVec ((h⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have e2 := (uext_mem_std _).1 ((hh _).1 (e1.symm ▸ hx))
    let z : Fin n → Lc.O := fun a => ⟨_, e2 a⟩
    have e0 : x = Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun a => (z a : Lc.K)) := e1.symm
    refine ⟨z, e0, ?_⟩
    have e3 : (⟨x, hx⟩ : Λ) = ∑ a, z a • b a := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change x = ∑ a, (z a : Lc.K) • Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Pi.single a 1)
      simp only [← Matrix.mulVec_smul]
      rw [← Matrix.mulVec_sum, e0]
      congr 1
      ext c
      simp [Finset.sum_apply, Pi.single_apply]
    have e4 : π x = π' ⟨x, hx⟩ := rfl
    rw [e4, e3, map_sum]
    exact Finset.sum_congr rfl fun a _ => hsmul (z a) _ (b a).2
  have hli : LinearIndependent F (fun a => π (b a)) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · intro y _
      obtain ⟨x, hx, rfl⟩ := hsurj y
      obtain ⟨z, -, hz⟩ := key x hx
      rw [hz]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · simp [hV]
  obtain ⟨z, hz1, hz2⟩ := key x hx
  have hz3 := Fintype.linearIndependent_iff.1 hli (fun a => Lc.res (z a)) (by rw [← hz2, h0])
  rw [hz1, ← Matrix.mulVec_smul, hh, uext_mem_std]
  intro a
  obtain ⟨y, hy⟩ := (Lc.res_ker _).1 (hz3 a)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hy, ← mul_assoc, inv_mul_cancel₀ Lc.q_ne, one_mul]
  exact y.2

theorem uext_mem_of_ne (p : PP Lc n) {x : Fin n → Lc.K} (hx : p.1.f x = 1) : x ∈ p.1.L := by
  by_contra h
  exact one_ne_zero (hx.symm.trans (p.2.off x h))

theorem uext_sub_mem {p p₁ : PP Lc n} {x y : Fin n → Lc.K} (hx : p.IsUp x p₁) (hy : p.IsUp y p₁) :
    ((q : Lc.K))⁻¹ • (x - y) ∈ p.1.L := by
  have h1 := uext_mem_of_ne p₁ hx.2.2
  have h2 := uext_mem_of_ne p₁ hy.2.2
  have h3 : ((q : Lc.K))⁻¹ • (x - y) ∈ p₁.1.L := by rw [smul_sub]; exact p₁.1.L.sub_mem h1 h2
  have h4 := p₁.2.add _ h3 _ h2
  rw [← smul_add, sub_add_cancel, hx.2.2, hy.2.2] at h4
  have h5 : ((q : Lc.K))⁻¹ • (x - y) ∈ p₁.ker := ⟨h3, by linear_combination -h4⟩
  rw [hx.2.1] at h5
  exact h5

theorem uext_isUp_of_sub {p p₁ : PP Lc n} {x y : Fin n → Lc.K} (hy : p.IsUp y p₁) (hx : x ∈ p.1.L)
    (hxy : ((q : Lc.K))⁻¹ • (x - y) ∈ p.1.L) : p.IsUp x p₁ := by
  refine ⟨hx, hy.2.1, ?_⟩
  have h2 := uext_mem_of_ne p₁ hy.2.2
  have h5 : ((q : Lc.K))⁻¹ • (x - y) ∈ p₁.ker := by rw [hy.2.1]; exact hxy
  have h4 := p₁.2.add _ h5.1 _ h2
  rw [← smul_add, sub_add_cancel, hy.2.2, h5.2, zero_add] at h4
  exact h4

end LocF

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ} (M : PtModel X i)

theorem PtModel.uext_piL_eq_iff (v : X.A.vT) (c : X.C.cls i) {x y : Fin (D.R.N i) → (M.Lc v).K}
    (hx : x ∈ ((M.rep c).2 v).1.L) (hy : y ∈ ((M.rep c).2 v).1.L) :
    M.piL v c x = M.piL v c y ↔ ((X.A.T : (M.Lc v).K))⁻¹ • (x - y) ∈ ((M.rep c).2 v).1.L := by
  have hxy := Submodule.sub_mem _ hx hy
  have e := M.piL_add v c _ hxy _ hy
  rw [sub_add_cancel] at e
  constructor
  · intro h
    obtain ⟨f, hf⟩ := ((M.rep c).2 v).2.lat
    refine LocF.uext_ker hf (X.fm.lv_rank i v c) (M.piL v c) (M.piL_add v c) (M.piL_smul v c) (M.piL_surj v c) hxy ?_
    rw [h] at e
    simpa using e
  · intro h
    have e2 := M.piL_smul v c (X.A.T : (M.Lc v).O) _ h
    have e3 : (M.Lc v).res (X.A.T : (M.Lc v).O) = 0 := ((M.Lc v).res_ker _).2 ⟨1, by simp⟩
    rw [e3, zero_smul, Subring.smul_def, smul_smul, Subring.coe_natCast, mul_inv_cancel₀ (M.Lc v).q_ne, one_smul] at e2
    rw [e, e2, zero_add]

theorem uop_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (v : X.A.vT) (φ : Fn X i)
    (Φ : M.Pt → M.Val), M.IsExt φ Φ → M.IsExt (Uop X i v φ) (fun p => ∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, Φ p₁) := by
  intro D u X i M v φ Φ hΦ
  obtain ⟨hfin, hact, huniq⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v
  constructor
  · intro c
    choose s hs1 hs2 using M.piL_surj v c
    have hf : ∀ y, X.fm.fv i v c y = 1 → ((M.rep c).2 v).1.f (s y) = 1 := by
      intro y hy
      rw [← M.piL_f v c _ (hs1 y), hs2, hy]
    let t : X.fm.lv i v c → LocF.PP (M.Lc v) (D.R.N i) := fun y =>
      if hy : X.fm.fv i v c y = 1 then (huniq (M.rep c) _ (hf y hy)).exists.choose else (M.rep c).2 v
    have ht : ∀ y, X.fm.fv i v c y = 1 → ((M.rep c).2 v).IsUp (s y) (t y) := by
      intro y hy
      simp only [t, dif_pos hy]
      exact (huniq (M.rep c) _ (hf y hy)).exists.choose_spec
    let P : X.fm.lv i v c → M.Pt := fun y => ((M.rep c).1, Function.update (M.rep c).2 v (t y))
    have hbij : Set.BijOn P
        ((Finset.univ.filter (fun x : X.fm.lv i v c => X.fm.fv i v c x = 1) : Finset _) : Set _)
        {p₁ | M.Inc v (M.rep c) p₁} := by
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        have hy' : X.fm.fv i v c y = 1 := by simpa using hy
        refine ⟨rfl, fun v' hv' => Function.update_of_ne hv' _ _, s y, hf y hy', ?_⟩
        simp only [P, Function.update_self]
        exact ht y hy'
      · intro y hy y' hy' e
        have h1 : X.fm.fv i v c y = 1 := by simpa using hy
        have h2 : X.fm.fv i v c y' = 1 := by simpa using hy'
        have e1 : t y = t y' := by
          have := congrFun (congrArg Prod.snd e) v
          simpa only [P, Function.update_self] using this
        have h3 := LocF.uext_sub_mem (ht y h1) (e1 ▸ ht y' h2)
        rw [← hs2 y, ← hs2 y']
        exact (M.uext_piL_eq_iff v c (hs1 y) (hs1 y')).2 h3
      · rintro p₁ ⟨h1, h2, x, hx1, hx2⟩
        have hy : X.fm.fv i v c (M.piL v c x) = 1 := by rw [M.piL_f v c x hx2.1, hx1]
        refine ⟨M.piL v c x, by simpa using hy, ?_⟩
        have h3 := LocF.uext_isUp_of_sub hx2 (hs1 _)
          ((M.uext_piL_eq_iff v c (hs1 _) hx2.1).1 (hs2 _))
        have h4 := (huniq (M.rep c) _ (hf _ hy)).unique (ht _ hy) h3
        refine Prod.ext h1.symm (funext fun v' => ?_)
        by_cases hv : v' = v
        · subst hv
          simp only [P, Function.update_self]
          exact h4
        · simp only [P, Function.update_of_ne hv]
          exact (h2 v' hv).symm
    have e1 := finsum_mem_eq_of_bijOn (f := fun y => Φ (P y)) (g := Φ) P hbij (fun _ _ => rfl)
    beta_reduce
    rw [← e1, finsum_mem_coe_finset, Submodule.coe_sum]
    simp only [Uop, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' : X.fm.fv i v c y = 1 := by simpa using hy
    obtain ⟨g, hg1, hg2⟩ := M.up_eq v c (s y) (t y) (hf y hy') (ht y hy')
    rw [hs2] at hg1 hg2
    rw [hΦ.1, hg2, ← hΦ.2, hg1]
  · intro g p
    have hbij : Set.BijOn (fun p₁ : M.Pt => g • p₁) {p₁ | M.Inc v p p₁} {p₁ | M.Inc v (g • p) p₁} := by
      refine ⟨fun p₁ h => (hact g p p₁).1 h, fun a _ b _ e => MulAction.injective g e, fun p₁ h => ?_⟩
      refine ⟨g⁻¹ • p₁, (hact g p _).2 ?_, smul_inv_smul g p₁⟩
      rw [smul_inv_smul]; exact h
    have e1 := finsum_mem_eq_of_bijOn (f := fun p₁ => M.act g (Φ p₁)) (g := Φ) _ hbij (fun a _ => (hΦ.2 g a).symm)
    beta_reduce
    rw [← e1, finsum_mem_eq_finite_toFinset_sum _ (hfin p).1, finsum_mem_eq_finite_toFinset_sum _ (hfin p).1, map_sum]

end GlobalTheory.LvT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValid
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

abbrev baseOfParams {D : D7} (L : SizeData₂ D) : Arith.Base :=
  { R := D.R, sc := L.sc, q := D.host.q, d := D.host.d, cls := D.host.cls, TT := D.host.TT, Sc := L.Sc, eta := L.etaSz }

theorem kapISet_eq_loc {D : D7} (L : SizeData₂ D) (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = Arith.Loc.kapISet (baseOfParams L) K p n' TT a b := rfl

theorem sig_eq_loc {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (hk : G.KapIDef X K)
    (hb : ∀ h t, X.bs h t = Arith.bsH h t) (a b : G.HH D → ℤ) (p : ℕ) :
    G.Sig X K a b p =
      Arith.Loc.Sig (baseOfParams L) (Arith.ins (baseOfParams L) K 1) K a b (G.hP D p) p := by
  have hb' : X.bs = Arith.bsH := by funext h t; exact hb h t
  have hk' : X.kapI = (Arith.ins (baseOfParams L) K 1).kapI := by
    funext p n' TT a b
    rw [hk p n' TT a b, kapISet_eq_loc]; rfl
  unfold G.Sig G.goodReps G.reps G.kapv G.kapLoc
  rw [hb', hk']
  rfl

theorem wreq_of_wok : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) → WOK p.L.sc cD ch C.GK H a b → Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK (G.aL p.L) (G.bL p.L) := by
  intro C cD ch p R H a b M c u0 _ hV hF hC h0 hW
  have hcl : p.D.host.cls = H.cls := hF.cls_eq
  obtain ⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, hw, -⟩ := hF
  subst hR
  have hTT' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have hh' : ∀ l, G.hP p.D l = hPH H l := fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  have ha : G.aL p.L = a := by
    funext t
    unfold G.aL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).1
    · exact (h0 t (hTT' ▸ h)).1.symm
  have hb : G.bL p.L = b := by
    funext t
    unfold G.bL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).2
    · exact (h0 t (hTT' ▸ h)).2.symm
  have hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ)) := by
    rw [p.L.Sc_eq, hV.Del_eq]; push_cast; rfl
  have key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A),
      p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) →
      (let B : Arith.Base := { R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta }
       open Classical in
       ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l *
        (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l then (1 : ℝ) else 0) +
          4 * Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l) ≤ p.L.sc.x ^ (-9 : ℝ)) →
      Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK a b := by
    intro q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6 hW
    obtain rfl : G.hP p.D = hf := funext e6
    subst e1 e2 e0 e3 e4 e5
    unfold Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands
    simp only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1]
    exact hW
  rw [ha, hb]
  exact key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh' hW

end GlobalTheory.EX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRational
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.Heis

theorem HV_conj {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) (x y : VV ι a b) :
    Formalism.L2.Ker.HV sc y x = (starRingEnd ℂ) (Formalism.L2.Ker.HV sc x y) := by
  simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem alpha_opU_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) (c : ℝ) (x y : V) (F : V → ℂ) (z : V) :
    alphaQ (c / 2) H x * opU H x (fun w => alphaQ (c / 2) H y * opU H y F w) z =
      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((c * (H x y).re + (H x y).im) / 2 : ℝ) : ℂ)) *
        (alphaQ (c / 2) H (x + y) * opU H (x + y) F z) := by
  simp only [alphaQ, opU, Formalism.L2.Th1.H.qOf]
  rw [← add_assoc z x y]
  have key : ∀ a b c d e f g u : ℂ, a + b + c + d = e + f + g →
      Complex.exp a * (Complex.exp b * (u * Complex.exp c) * Complex.exp d) =
        Complex.exp e * (Complex.exp f * (u * Complex.exp g)) := by
    intro a b c d e f g u h
    have : Complex.exp a * Complex.exp b * Complex.exp c * Complex.exp d =
        Complex.exp e * Complex.exp f * Complex.exp g := by
      simp only [← Complex.exp_add, h]
    linear_combination u * this
  apply key
  simp only [map_add, LinearMap.add_apply]
  rw [hH x y]
  have h1 : H x y = ((H x y).re : ℂ) + ((H x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : (starRingEnd ℂ) (H x y) = ((H x y).re : ℂ) - ((H x y).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Complex.add_re, Complex.conj_re]
  rw [h2]
  generalize (H x y).re = r at *
  generalize (H x y).im = s at *
  rw [h1]
  push_cast
  ring

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add _ x y

theorem Wx_Wx (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z := by
  funext z
  have := alpha_opU_mul (Formalism.L2.Ker.HV A.sc) (fun x y => HV_conj A.sc x y) (Real.sqrt A.d) (emb A x) (emb A y) F z
  rw [← emb_add] at this
  exact this

theorem imH_eq (x y : HomE X.E a b) : imH A x y = coc A x y - coc A y x := by
  simp only [coc, imH, altE]
  rw [HV_conj A.sc (emb A x) (emb A y)]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

theorem imH_add_left (x y z : HomE X.E a b) : imH A (x + y) z = imH A x z + imH A y z := by
  simp only [imH, altE, emb_add, map_add, LinearMap.add_apply, Complex.add_im]

theorem imH_add_right (x y z : HomE X.E a b) : imH A x (y + z) = imH A x y + imH A x z := by
  simp only [imH, altE, emb_add, map_add, LinearMap.add_apply, Complex.add_im]

theorem Wx_comm (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z := by
  rw [Wx_Wx, Wx_Wx, add_comm y x]
  funext z
  have : brkE A y x = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A x y : ℂ)) := rfl
  rw [this, ← mul_assoc, ← Complex.exp_add, imH_eq]
  congr 2
  push_cast
  ring

theorem contDiff_Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) (k : ℕ) (hF : ContDiff ℂ k F) :
    ContDiff ℂ k (Wx A x F) := by
  have h : ContDiff ℂ k (fun z : VCx X.Tau a b => Formalism.L2.Ker.HV A.sc z (emb A x)) := by
    simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply]
    fun_prop
  unfold Wx opU
  exact contDiff_const.mul ((hF.comp (contDiff_id.add contDiff_const)).mul
    (((contDiff_const.mul h).sub contDiff_const).cexp))

theorem jetC_sum (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ)
    (hF : ∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) (m : DVar X.Tau a b →₀ ℕ) :
    jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m := by
  classical
  have hd : ∀ n : ℕ, iteratedFDeriv ℂ n (fun z => ∑ i ∈ T, c i * F i z) 0 = ∑ i ∈ T, c i • iteratedFDeriv ℂ n (F i) 0 := by
    intro n
    have e : (fun z => ∑ i ∈ T, c i * F i z) = ∑ i ∈ T, c i • F i := by
      funext z; simp
    rw [e, iteratedFDeriv_sum_apply (f := fun i => c i • F i) (fun i hi => ((hF i hi n).const_smul (c i)).contDiffAt)]
    exact Finset.sum_congr rfl fun i hi => iteratedFDeriv_const_smul_apply (hF i hi n).contDiffAt
  simp only [jetC, derivAt0, hd, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem calculus : ∀ (X : Fields) (A : Amb X) (a b : ℕ), (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z) ∧ (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z) ∧ (∀ x y : HomE X.E a b, imH A x y = coc A x y - coc A y x) ∧ (∀ x y z : HomE X.E a b, coc A (x + y) z = coc A x z + coc A y z ∧ coc A x (y + z) = coc A x y + coc A x z ∧ imH A (x + y) z = imH A x z + imH A y z ∧ imH A x (y + z) = imH A x y + imH A x z) ∧ (∀ y t : HomE X.E a b, brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ))) ∧ (∀ y t : HomE X.E a b, brkE A y t = 1 ↔ ∃ n : ℤ, imH A t y = n) ∧ (∀ (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ), (∀ k : ℕ, ContDiff ℂ k F) → ∀ k : ℕ, ContDiff ℂ k (Wx A x F)) ∧ (∀ (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ), (∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) → ∀ m, jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m) := by
  intro X A a b
  refine ⟨Wx_Wx A, Wx_comm A, imH_eq A, fun x y z => ⟨?_, ?_, imH_add_left A x y z, imH_add_right A x y z⟩,
    fun _ _ => rfl, fun y t => ?_, fun x F hF k => contDiff_Wx A x F k (hF k), fun κ T c F hF m => jetC_sum A κ T c F hF m⟩
  · simp only [coc, imH_add_left, emb_add, map_add, LinearMap.add_apply, Complex.add_re]; ring
  · simp only [coc, imH_add_right, emb_add, map_add, LinearMap.add_apply, Complex.add_re]; ring
  · have : brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ)) := rfl
    rw [this, Complex.exp_eq_one_iff]
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      have : ((imH A t y : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination -hn
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [hn]
      push_cast
      ring

end GlobalTheory.MomT.Heis
end
end

