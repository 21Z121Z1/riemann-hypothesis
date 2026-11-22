import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.DataForced
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.InertJacobiLevels.TiesView
import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLk
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV NumberField

variable {D : D7} {L : SizeData₂ D}

theorem ptB_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ptB D u := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ptB
  exact Finset.prod_nonneg fun τ _ => mul_nonneg (by positivity) (sq_nonneg _)

theorem pSq_le_ptB (D : D7) (u : D.what₂.Word) (h6 : Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) (h : (D.fm u).PRat) (s : D.what₂.LL →+* ℂ) :
    Formalism.MainNotions.LocalQuadraticParts.pSq D u h s ≤ Formalism.MainNotions.product_first_zeroth_parts.ptB D u := by
  obtain ⟨_, _, _, ⟨h', _, hb⟩, _⟩ := h6
  exact opNormAt_sq_le _ _ _ _ ((D.fm u).lat_good D.R.m).1 (InfinitePlace.mk s)
    (IsTotallyComplex.isComplex _) ((D.fm u).PtL h) _ (ptB_nonneg D u) (hb (InfinitePlace.mk s))

def PtBSize (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop := ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ptB D u ≤ Real.exp (SZbP D L C u)

theorem normSq_le_exp_of_level_norm {C : ℝ} (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) (hS : PtBSize D L C) :
    ∀ u (h : (D.fm u).PRat) s, Formalism.MainNotions.LocalQuadraticParts.pSq D u h s ≤ Real.exp (SZbP D L C u) := by
  intro u h s
  exact (pSq_le_ptB D u (h6 u) h s).trans (hS u)

def SZKer (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u i (h : (D.fm u).KRat i), i + 1 ≤ D.R.m → Formalism.MainNotions.placeRankTwoOne.kLe D u i h (kernelPlaceMeanBound D L C u (i + 1))

def APlusShape (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ ρ,
    (∀ i i', i ≤ i' → i' < (D.R.sigW j).1 → aPlus D j ρ i' ≤ aPlus D j ρ i) ∧
    ∀ i, D.R.k - 1 ≤ i → i < (D.R.sigW j).1 → aPlus D j ρ i ≤ L.etaSz

theorem size_bounds_of_kernels_and_norms {C : ℝ} (h1 : SZKer D L C) (h3 : APlusShape D L) (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u)
    (hS : PtBSize D L C) : Formalism.MainNotions.LocalQuadraticParts.adm7 D L C := by
  unfold Formalism.MainNotions.LocalQuadraticParts.adm7
  exact ⟨h1, normSq_le_exp_of_level_norm h6 hS, h3⟩

theorem ETDef_of {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : ∀ u (i : Fin 2), D.host.g i ≠ (D.mem u).A.T) : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ETDef D u L := by
  intro u w hw
  have hw' : D.what₂.places.resChar w = (D.mem u).A.T := hw
  have hs : D.host.cls (D.what₂.places.resChar w) = PrimeClass.splitK := by
    rw [hw']; exact P.level_split _ (D.T_level u)
  obtain ⟨hg, ht, _⟩ := L.not_inert w (by rw [hs]; exact fun h => by cases h) (by rw [hs]; exact fun h => by cases h)
  refine ⟨ht, fun j hj => ⟨hg j, ?_, ?_⟩⟩
  · rw [hF j hj w]
    unfold Fval FvalP
    have h1 : D.what₂.places.resChar w ∉ L.gTypes := by
      rw [hw']
      simp only [SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hTg u 0 h.symm, fun h => hTg u 1 h.symm⟩
    have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by rw [hs]; exact fun h => by cases h
    have h3 : ¬ ((Formalism.MainNotions.G.IsResidueClassZero D (D.what₂.places.resChar w) ∨ Formalism.MainNotions.G.IsSg D (D.what₂.places.resChar w)) ∧
        (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := by
      rintro ⟨h | h, _⟩
      · exact absurd (hs.symm.trans h) (fun h => by cases h)
      · exact absurd (hs.symm.trans h) (fun h => by cases h)
    rw [if_neg h1, if_neg h2, if_neg h3]
  · rw [hE u j hj w]
    unfold Eval
    simp only [hw', if_true]

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLw
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem kernels_rational_over_coefficients (D : D7) (hK : StandardLatticesGL3.kRat D) (h6 : ∀ u, product_first_zeroth_parts.Conclusion6 D u) : LocalQuadraticParts.KernelRationality D :=
  ⟨hK, fun u => by
    obtain ⟨_, _, _, ⟨h, _⟩, _⟩ := h6 u
    exact h⟩

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSaa
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab

def SameServed (K : G.Consts) (A A' : GAll) (p : ℕ) : Prop :=
  (GC.VV A.X K A.a A.b p).image Formalism.HC.Frame.A.val = (GC.VV A'.X K A'.a A'.b p).image Formalism.HC.Frame.A.val ∧
  GC.Sig A.X K A.a A.b p = GC.Sig A'.X K A'.a A'.b p ∧
  GC.tauP A.X K A.a A.b p = GC.tauP A'.X K A'.a A'.b p ∧
  GC.ioP A.X K A.a A.b p = GC.ioP A'.X K A'.a A'.b p ∧
  ∀ t0 ∈ GC.VV A.X K A.a A.b p, ∀ t0' : GC.HH A'.D, t0.val = t0'.val →
    GC.kapv A.X K A.a A.b p t0 = GC.kapv A'.X K A'.a A'.b p t0' ∧
    GC.Sv A.X K A.a A.b p t0 = GC.Sv A'.X K A'.a A'.b p t0'

theorem sameServed (K : G.Consts) (A A' : GAll) (hR : A.D.R = A'.D.R)
    (hTT : A.D.host.TT.image Formalism.HC.Frame.A.val = A'.D.host.TT.image Formalism.HC.Frame.A.val)
    (hcls : A.D.host.cls = A'.D.host.cls) (hhP : ∀ p, (A.D.hPf p).val = (A'.D.hPf p).val)
    (hsc : A.L.sc = A'.L.sc) (hSc : A.L.Sc = A'.L.Sc) (heta : A.L.etaSz = A'.L.etaSz)
    (hbs : ∀ (h t : GC.HH A.D) (h' t' : GC.HH A'.D), h.val = h'.val → t.val = t'.val →
      (A.X.bs h t).val = (A'.X.bs h' t').val)
    (hoff : ∀ j (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.X.off j (false, t) = A'.X.off j (false, t'))
    (hkap : A.X.kapI = A'.X.kapI) (hep : A.X.ep = A'.X.ep)
    (ha : ∀ (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.a t = A'.a t')
    (hb : ∀ (t : GC.HH A.D) (t' : GC.HH A'.D), t.val = t'.val → A.b t = A'.b t') (p : ℕ) :
    SameServed K A A' p := by
  obtain ⟨⟨R, ⟨TT, T2, u0, cls⟩, hPf⟩, ⟨sc, Sc, η⟩, ⟨bs, h1, h2, off, h3, h4, h5, kapI, ep⟩, a, b⟩ := A
  obtain ⟨⟨R', ⟨TT', T2', u0', cls'⟩, hPf'⟩, ⟨sc', Sc', η'⟩, ⟨bs', h1', h2', off', h3', h4', h5', kapI', ep'⟩, a', b'⟩ := A'
  simp only at hR
  subst hR
  simp only at hTT hcls hhP hsc hSc heta hbs hoff hkap hep ha hb
  have eTT : TT = TT' := Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have ehP : hPf = hPf' := funext fun p => Formalism.HC.Frame.A.val_injective _ (hhP p)
  have ebs : bs = bs' := funext fun h => funext fun t => Formalism.HC.Frame.A.val_injective _ (hbs h t h t rfl rfl)
  have ea : a = a' := funext fun t => ha t t rfl
  have eb : b = b' := funext fun t => hb t t rfl
  subst eTT hcls ehP hsc hSc heta ebs hkap hep ea eb
  have hoff' : ∀ j t, off j (false, t) = off' j (false, t) := fun j t => hoff j t t rfl
  let D1 : GC.GD := ⟨R, ⟨TT, T2, u0, cls⟩, hPf⟩
  let D2 : GC.GD := ⟨R, ⟨TT, T2', u0', cls⟩, hPf⟩
  let X1 : GC.Inst D1 ⟨sc, Sc, η⟩ := ⟨bs, h1, h2, off, h3, h4, h5, kapI, ep⟩
  let X2 : GC.Inst D2 ⟨sc, Sc, η⟩ := ⟨bs, h1', h2', off', h3', h4', h5', kapI, ep⟩
  have eVV : GC.VV X1 K a b p = GC.VV X2 K a b p := rfl
  have eSig : GC.Sig X1 K a b p = GC.Sig X2 K a b p := rfl
  have eTau : GC.tauP X1 K a b p = GC.tauP X2 K a b p := rfl
  have eKap : ∀ t0, GC.kapv X1 K a b p t0 = GC.kapv X2 K a b p t0 := fun _ => rfl
  have eSv : cls p = PrimeClass.inertClass → ∀ t0, GC.Sv X1 K a b p t0 = GC.Sv X2 K a b p t0 := by
    intro hc0 t0
    have hp1 : ∀ s e, GC.partner D1 p s e = (false, s + e • hPf p) := by
      intro s e
      show (decide (cls p = PrimeClass.signal ∧ Odd e), s + e • hPf p) = _
      simp [hc0]
    have hp2 : ∀ s e, GC.partner D2 p s e = (false, s + e • hPf p) := by
      intro s e
      show (decide (cls p = PrimeClass.signal ∧ Odd e), s + e • hPf p) = _
      simp [hc0]
    have hfG : ∀ j s, GC.fillG X1 b j (false, s) = GC.fillG X2 b j (false, s) := by
      intro j s
      show (_ + off j (false, s)) - _ = (_ + off' j (false, s)) - _
      rw [hoff']
      rfl
    have hcap : ∀ j s e, GC.capU X1 b p j s e = GC.capU X2 b p j s e := by
      intro j s e
      unfold GC.capU
      rw [hp1, hp2, hfG]
      rfl
    unfold GC.Sv GC.gU GC.g0 GC.Pr
    simp only [hcap, hfG]
    rfl
  have hC0 : (GC.VV X1 K a b p).Nonempty → cls p = PrimeClass.inertClass := by
    intro hne
    by_contra hn
    have : GC.VV X1 K a b p = ∅ := by
      unfold GC.VV
      rw [if_neg]
      rintro ⟨hc, _⟩
      exact hn hc.2.2.1
    rw [this] at hne
    exact Finset.not_nonempty_empty hne
  refine ⟨congrArg (Finset.image Formalism.HC.Frame.A.val) eVV, eSig, eTau, ?_, ?_⟩
  · show GC.ioP X1 K a b p = GC.ioP X2 K a b p
    by_cases hne : (GC.VV X1 K a b p).Nonempty
    · have hne2 : (GC.VV X2 K a b p).Nonempty := hne
      unfold GC.ioP
      rw [dif_pos hne, dif_pos hne2, eSig]
      congr 1
      exact Finset.sup'_congr hne rfl fun t0 _ => eSv (hC0 hne) t0
    · have hne2 : ¬ (GC.VV X2 K a b p).Nonempty := hne
      unfold GC.ioP
      rw [dif_neg hne, dif_neg hne2]
  · show ∀ t0 ∈ GC.VV X1 K a b p, ∀ t0' : GC.HH D2, t0.val = t0'.val →
      GC.kapv X1 K a b p t0 = GC.kapv X2 K a b p t0' ∧ GC.Sv X1 K a b p t0 = GC.Sv X2 K a b p t0'
    intro t0 ht0 t0' htt
    have : t0 = t0' := Formalism.HC.Frame.A.val_injective _ htt
    subst this
    exact ⟨eKap t0, eSv (hC0 ⟨t0, ht0⟩) t0⟩

variable {eps : ℝ} (Fm : FamP eps)

theorem served_orbit_counts_agree (x : ℝ) (hx : Fm.x1 < x) : Formalism.MainNotions.LocalQuadraticParts.AmbientMetricLowerBound Fm x := by
  intro i i' a b u0 u0' hr hr' p
  have hTT : (Fm.D x i).host.TT.image Formalism.HC.Frame.A.val = (Fm.D x i').host.TT.image Formalism.HC.Frame.A.val :=
    (Fm.TT_eq x i).trans (Fm.TT_eq x i').symm
  have hR := Fm.R_eq x i i'
  have hsc : (Fm.L x i).sc = (Fm.L x i').sc := by
    have e1 : (Fm.L x i).sc.x = (Fm.L x i').sc.x := by rw [Fm.L_x x i hx, Fm.L_x x i' hx]
    have e2 : (Fm.L x i).sc.eps = (Fm.L x i').sc.eps := by rw [Fm.L_eps x i, Fm.L_eps x i']
    have e3 : (Fm.L x i).sc.J = (Fm.L x i').sc.J := (Fm.L_J x i).trans (Fm.L_J x i').symm
    cases h1 : (Fm.L x i).sc
    cases h2 : (Fm.L x i').sc
    rw [h1, h2] at e1 e2 e3
    simp only at e1 e2 e3
    subst e1 e2 e3
    rfl
  exact sameServed Fm.GK (allOf (Fm.Gx x i)) (allOf (Fm.Gx x i')) hR hTT
    (host_cls_eq (Fm.q_eq x i i') (Fm.d_eq x i i') (Fm.QS_eq x i i'))
    (Fm.hP_eq x i i') hsc (Fm.Sc_shared x i i') (Fm.eta_eq x i i') (Fm.bs_eq x i i') (Fm.off_eq x i i')
    (Fm.kapI_eq x i i') (Fm.ep_eq x i i')
    (fun t t' ht => extension_by_zero_val_eq (congrArg (fun R : Ranks => R.e) hR) hTT _ _
      (fun s s' hs => by rw [(hr.2 s).1, (hr'.2 s').1, hs]) t t' ht)
    (fun t t' ht => extension_by_zero_val_eq (congrArg (fun R : Ranks => R.e) hR) hTT _ _
      (fun s s' hs => by rw [(hr.2 s).2, (hr'.2 s').2, hs]) t t' ht) p

theorem family_served_orbit_counts_agree : Formalism.MainNotions.LocalQuadraticParts.BaseIndependenceFamily Fm := fun x hx => served_orbit_counts_agree Fm x hx

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSl
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

variable {D : D7} {L : SizeData₂ D}

theorem served_prime_lattices (Gi : Inst D L) (K : Consts) (C bo : ℝ) (h : LinkG_at Gi K C bo) : Formalism.MainNotions.LocalQuadraticParts.adm18 Gi K :=
  ⟨h.1, h.2.1⟩

theorem family_served_prime_lattices {eps : ℝ} (Fm : FamP eps) (h : LinkG Fm) : Formalism.MainNotions.LocalQuadraticParts.G1Family Fm := by
  obtain ⟨C, x0, δ, _, H⟩ := h
  exact ⟨x0, fun x hx i => served_prime_lattices _ _ C _ (H x hx i)⟩

theorem served_orbits_band_bad_probability (Gi : Inst D L) (K : Consts) (Cb : ℝ) (h33 : Formalism.MainNotions.CornerGLContinuity.OrdersLargePrimeBound D L K)
    (h32 : Formalism.MainNotions.CornerGLContinuity.BadPrimeBound D L Gi Cb) : Formalism.MainNotions.LocalQuadraticParts.adm20 Gi K Cb :=
  ⟨served_orbits_in_set Gi K _ _, h33.2.2.2.1, h32⟩

theorem family_served_orbits_band {eps : ℝ} (Fm : FamP eps) (h33 : Formalism.MainNotions.CornerGLContinuity.FamilyOrdersLargePrimeBoundConstant Fm) (h32 : Formalism.MainNotions.CornerGLContinuity.FamilyBadPrimeBound Fm) :
    Formalism.MainNotions.LocalQuadraticParts.G3BoundFamily Fm := by
  obtain ⟨x0, h0⟩ := h33
  obtain ⟨Cb, _, x1, h1⟩ := h32
  exact ⟨Cb, max x0 x1, fun x hx i => served_orbits_band_bad_probability _ _ Cb (h0 x (le_trans (le_max_left _ _) hx) i)
    (h1 x (le_trans (le_max_right _ _) hx) i)⟩

theorem family_mean_shares_windows {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.AuxBlock8.ConclusionOnFamily Fm Fm.GK Fm.Gx) : Formalism.MainNotions.LocalQuadraticParts.FontaineFormalPropertiesFamily Fm := by
  obtain ⟨C, δ, _, x0, H⟩ := h
  exact ⟨x0, fun x hx i => (H x hx i).2.1⟩

def ExcSplit (L : SizeData₂ D) : Prop :=
  ∀ u p, p.Prime → Formalism.MainNotions.LocalQuadraticParts.Exc L u p → p = D.host.d ∨ ¬ InertK D p

theorem sizes_depths_thresholds (Gi : Inst D L) (K : Consts) (C bo : ℝ) (h1 : Formalism.MainNotions.CornerGLContinuity.CutSizes D L Gi K C)
    (h2 : Formalism.MainNotions.CornerGLContinuity.WeightSumBound D L C bo) (h3 : ExcSplit L) : Formalism.MainNotions.LocalQuadraticParts.HerrCocycleExtensionClass Gi K C bo :=
  ⟨h1, h2, h3⟩

theorem sc_a_pos (s : Scale) : 1 < s.a := by
  have hx := s.one_lt_alt
  have hb : 1 ≤ s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  unfold Scale.a
  nlinarith

theorem tau_size_bound_mono (Gi : Inst D L) (K : Consts) {C C' : ℝ} (hC : C ≤ C')
    (h : Formalism.MainNotions.CornerGLContinuity.CutSizes D L Gi K C) : Formalism.MainNotions.CornerGLContinuity.CutSizes D L Gi K C' := by
  have ha : 0 < L.sc.a := lt_trans one_pos (sc_a_pos L.sc)
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  refine ⟨fun t0 ht => ?_, fun hV => ?_⟩
  · have hn : 0 ≤ (Nv Gi p t0 : ℝ) * L.sc.a / (p : ℝ) := by positivity
    have e : ∀ c : ℝ, c * (Nv Gi p t0 : ℝ) * L.sc.a / (p : ℝ) = c * ((Nv Gi p t0 : ℝ) * L.sc.a / (p : ℝ)) :=
      fun c => by ring
    have hm := mul_le_mul_of_nonneg_right hC hn
    have h1' := h1 t0 ht
    rw [e C']
    rw [e C] at h1'
    exact ⟨le_trans h1'.1 hm, le_trans h1'.2 hm⟩
  · have hl : 0 ≤ Real.logb p L.sc.a := by
      rcases Nat.lt_or_ge 1 p with h1p | h1p
      · exact Real.logb_nonneg (by exact_mod_cast h1p) (sc_a_pos L.sc).le
      · interval_cases p <;> simp [Real.logb]
    have hn : 0 ≤ (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a := by positivity
    have e : ∀ c : ℝ, c * D.R.f * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a =
        c * ((D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a) := fun c => by ring
    rw [e C']
    have := h2 hV
    rw [e C] at this
    exact le_trans this (mul_le_mul_of_nonneg_right hC hn)

theorem tau_sum_bound_mono {C C' bo : ℝ} (hC : C ≤ C') (h : Formalism.MainNotions.CornerGLContinuity.WeightSumBound D L C bo) : Formalism.MainNotions.CornerGLContinuity.WeightSumBound D L C' bo := by
  have ha : 0 < L.sc.a := lt_trans one_pos (sc_a_pos L.sc)
  have hX : 0 ≤ Real.log L.sc.X' := by
    unfold Scale.X'
    rw [Real.log_exp]
    exact Real.rpow_nonneg (lt_trans one_pos L.sc.one_lt_alt).le _
  have hn : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X' := by positivity
  have e : ∀ c : ℝ, c * D.R.m * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X' =
      c * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X') := fun c => by ring
  unfold Formalism.MainNotions.CornerGLContinuity.WeightSumBound at h ⊢
  rw [e C']
  rw [e C] at h
  linarith [mul_le_mul_of_nonneg_right hC hn]

theorem family_sizes_depths_thresholds {eps : ℝ} (Fm : FamP eps) (h1 : Formalism.MainNotions.CornerGLContinuity.FamilyCutSizes Fm) (h2 : Formalism.MainNotions.CornerGLContinuity.FamilyWeightSumBound Fm)
    (h3 : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ExcSplit (Fm.L x i)) : Formalism.MainNotions.LocalQuadraticParts.AddedTermFamily Fm := by
  obtain ⟨C1, x1, H1⟩ := h1
  obtain ⟨C2, x2, δ, hδ, H2⟩ := h2
  obtain ⟨x3, H3⟩ := h3
  refine ⟨max C1 C2, max x1 (max x2 x3), δ, hδ, fun x hx i => ?_⟩
  have a1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have a2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have a3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  exact sizes_depths_thresholds _ _ _ _ (tau_size_bound_mono _ _ (le_max_left _ _) (H1 x a1 i))
    (tau_sum_bound_mono (le_max_right _ _) (H2 x a2 i)) (H3 x a3 i)

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem cc_l : PowerSeries.constantCoeff g.l = 0 := by
  unfold G1.l
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.TaylorLogMetric.flog, PowerSeries.coeff_mk, if_pos rfl]

private theorem cc_subst_lemma {R : Type} [CommRing R] {υ : Type} {a : MvPowerSeries υ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst hs]
  refine (finsum_congr fun d => ?_).trans finsum_zero
  rcases d with _ | d
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_smul]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow (Nat.succ_ne_zero d), smul_zero]

private theorem comp_lemma_2 {υ ρ : Type} {R : Type} [CommRing R] {a : MvPowerSeries υ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {c : υ → MvPowerSeries ρ R} (hc : HasSubst c)
    (f : PowerSeries R) : subst c (PowerSeries.subst a f) = PowerSeries.subst (subst c a) f := by
  have ha' : HasSubst (fun _ : Unit => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply ha' hc]

theorem cc_lg {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) : constantCoeff (g.lg a) = 0 :=
  cc_subst_lemma ha (cc_l g)

theorem cc_pt (hex : PowerSeries.constantCoeff g.ex = 0) {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) :
    constantCoeff (g.pt a) = 0 :=
  cc_subst_lemma ha hex

theorem lg_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.lg a) = g.lg (subst c a) :=
  comp_lemma_2 ha hc g.l

theorem pt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.pt a) = g.pt (subst c a) :=
  comp_lemma_2 ha hc g.ex

theorem phAt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.phAt a) = g.phAt (subst c a) :=
  comp_lemma_2 ha hc g.ph

theorem add_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.add a b) = g.add (subst c a) (subst c b) := by
  have h0 : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add, cc_lg g ha, cc_lg g hb, add_zero]
  show subst c (g.pt (g.lg a + g.lg b)) = g.pt (g.lg (subst c a) + g.lg (subst c b))
  rw [pt_subst g hc h0, ← coe_substAlgHom hc, map_add, coe_substAlgHom, lg_subst g hc ha, lg_subst g hc hb]

theorem cc_add (hex : PowerSeries.constantCoeff g.ex = 0) {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : constantCoeff (g.add a b) = 0 :=
  cc_pt g hex (by rw [map_add, cc_lg g ha, cc_lg g hb, add_zero])

theorem be_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.be a b) = g.be (subst c a) (subst c b) := by
  have hab := cc_add g hex ha hb
  show subst c (g.phAt (g.add a b) - g.phAt a - g.phAt b) =
    g.phAt (g.add (subst c a) (subst c b)) - g.phAt (subst c a) - g.phAt (subst c b)
  rw [← coe_substAlgHom hc, map_sub, map_sub, coe_substAlgHom, phAt_subst g hc hab, phAt_subst g hc ha,
    phAt_subst g hc hb, add_subst g hex hc ha hb]

theorem dg_Cmul (ep : ℂ_[p]) (i : σ) :
    (diagS (PowerSeries.C ep * g.l) i : MvPowerSeries σ ℂ_[p]) = C ep * g.lg (X i) := by
  have hX : PowerSeries.HasSubst (X i : MvPowerSeries σ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)
  unfold diagS G1.lg
  rw [← PowerSeries.smul_eq_C_mul, ← smul_eq_C_mul, ← PowerSeries.coe_substAlgHom hX, map_smul]

theorem cc_Cl (ep : ℂ_[p]) : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
  rw [map_mul, cc_l g, mul_zero]

end G1

section Lin

variable {Z E Kap : Type} {R : Type} [CommRing R]

def IsLin [Fintype Z] (f : MvPowerSeries Z R) : Prop :=
  f = ∑ z, C (coeff (Finsupp.single z 1) f) * X z

theorem isLin_sum [Fintype Z] {α : Type} (s : Finset α) (f : α → MvPowerSeries Z R) (h : ∀ a ∈ s, IsLin (f a)) :
    IsLin (∑ a ∈ s, f a) := by
  unfold IsLin at *
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl h

end Lin

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVi
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem family_scale_epsilon_condition {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.ArithmeticCylinders.FamilyExpDeficitBound' Fm) : Formalism.MainNotions.LocalQuadraticParts.IrreducibilityFamily Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx)
  have := h x (le_trans (le_max_left _ _) hx) i
  unfold Formalism.MainNotions.LocalQuadraticParts.adm22
  rw [Fm.L_x x i hx1, Fm.L_ez x i]
  exact this

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVq
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem good_twists_condition (D : D7) (N : NChoice D) (I : Formalism.MainNotions.TwIn D) (h : Formalism.MainNotions.TwGoodAt D N I) :
    Formalism.MainNotions.LocalQuadraticParts.TwistConductorsSplit D N := by
  classical
  intro w hw v hv
  obtain ⟨hs, hd, -⟩ := (h w hw).2.1
  refine ⟨(hs v hv).1, fun hp => ?_⟩
  have h0 : v ∈ D.ntw.S0 (N.twI w) := by
    have h1 := D.ntw.twistExcludedPlaces_contains_residueChar (N.twI w)
    rw [N.twI_l w] at h1
    exact_mod_cast h1 hp
  exact Finset.disjoint_left.mp hd hv (Finset.mem_union_left _ h0)

theorem family_good_twists_condition {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TwGood Fm) : Formalism.MainNotions.LocalQuadraticParts.TwistConductorsFamily Fm := by
  obtain ⟨x0, H⟩ := h
  refine ⟨x0, fun x hx0 hx i => ?_⟩
  obtain ⟨-, N0, S, hG⟩ := H x hx0 hx i
  exact good_twists_condition _ _ _ hG

end Formalism.MainNotions.J

end
end

