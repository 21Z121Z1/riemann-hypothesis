import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BesselPeriodPositionOneEqZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.BesselGap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Tri (D : D7) : Type 1 := (A : HSp D) × (B : HSp D) × (A.V →ₗ[D.host.E] B.V)

def tri0 (D : D7) : Tri D := ⟨D.sp.X 0, D.sp.Y 0, D.sp.iXY 0⟩

def Pos' (X : ThetaX D) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type :=
  {_q : X.Pos (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) × Bool // (⟨A, B, ι⟩ : Tri D) = tri0 D}

def where₂ (X : ThetaX D) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (q : Pos' X A B ι) : X.Pos A B ι :=
  cast (congrArg (fun τ : Tri D => X.Pos τ.1 τ.2.1 τ.2.2) q.2.symm) q.1.1

open Classical in

def emb (X : ThetaX D) (t j : ℕ) : (X.Xs t j).V →ₗ[D.host.E] (X.Ys t j).V :=
  if (⟨X.Xs t j, X.Ys t j, X.iXYs t j⟩ : Tri D) = tri0 D then -X.iXYs t j else X.iXYs t j

theorem emb_isom (X : ThetaX D) (t j : ℕ) (hj : j < D.R.m) : HSpace.IsIsomEmb (X.Xs t j) (X.Ys t j) (emb X t j) := by
  intro x y
  unfold emb
  split_ifs
  · simpa using X.iXYs_isom t j hj x y
  · exact X.iXYs_isom t j hj x y

theorem emb_ne (X : ThetaX D) (t j : ℕ) (hj : j < D.R.m) :
    (⟨X.Xs t j, X.Ys t j, emb X t j⟩ : Tri D) ≠ tri0 D := by
  unfold emb
  split_ifs with h
  · intro h'
    have h2 := h'.trans h.symm
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h2
    have h0 : ∀ x, X.iXYs t j x = 0 := by
      intro x
      have h3 : -X.iXYs t j x = X.iXYs t j x := by simpa using LinearMap.congr_fun h2 x
      have h4 : (2 : D.host.E) • X.iXYs t j x = 0 := by
        rw [two_smul]; nth_rewrite 1 [← h3]; exact neg_add_cancel _
      exact (smul_eq_zero.1 h4).resolve_left two_ne_zero
    have hz : ∀ x : (X.Xs t j).V, x = 0 := by
      intro x
      refine (X.Xs t j).nondeg.1 x fun y => ?_
      rw [← X.iXYs_isom t j hj x y, h0, h0]; simp
    have hr : (X.Xs t j).rank = 0 := by
      rw [← (X.Xs t j).rank_eq]
      have : Subsingleton (X.Xs t j).V := ⟨fun a b => (hz a).trans (hz b).symm⟩
      exact Module.finrank_zero_of_subsingleton
    have := X.Xs_rank t j hj.le
    have := D.R.m_add_three_le_k
    omega
  · exact h

def cut (X : ThetaX D) : ThetaX D :=
  { X with
    iXYs := emb X
    iXYs_isom := emb_isom X
    Pos := Pos' X
    Bper := fun A B ι q s φ F => if q.1.2 then X.Bper A B ι (where₂ X q) s φ F else 0
    Bper_right := fun A B ι q s φ => by
      cases h : q.1.2
      · exact ⟨by simp, by simp⟩
      · simpa using X.Bper_right A B ι (where₂ X q) s φ
    Bper_add_left := fun A B ι q s φ φ' F => by
      split_ifs
      · exact X.Bper_add_left ..
      · simp
    Bper_smul_left := fun A B ι q s c φ F => by
      split_ifs
      · exact X.Bper_smul_left ..
      · simp
    Bper_odd := fun A B ι q ho s s' φ F => by
      split_ifs
      · exact X.Bper_odd _ _ _ _ ho ..
      · rfl
    pos1 := fun u => ⟨(X.pos1 u, false), rfl⟩
    posSym := fun u => ⟨(X.posSym u, true), rfl⟩ }

def cutT {X : ThetaX D} (T : ThetaTied D X) : ThetaTied D (cut X) := { T with }

def cutW {X : ThetaX D} {T : ThetaTied D X} (W : WeilTied D X T) : WeilTied D (cut X) (cutT T) :=
  { W with om_tw := ⟨W.om_tw.1, W.om_tw.2, W.om_tw.3, W.om_tw.4⟩ }

def cutB {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} (B : BesselTied D X T W) :
    BesselTied D (cut X) (cutT T) (cutW W) where
  dat A B' ι ho q := B.dat A B' ι ho (where₂ X q)
  dat_y A B' ι ho q := B.dat_y A B' ι ho (where₂ X q)
  besC A B' ι q := B.besC A B' ι (where₂ X q)
  besC_pos A B' ι q := B.besC_pos A B' ι (where₂ X q)
  besC_one A B' ι q := B.besC_one A B' ι (where₂ X q)
  bper A B' ι ho hr hs hi q hq sF μ 𝓕 hv μN 𝓕N h1 h2 h3 s hs' φ F hφ := by
    obtain ⟨u, hu⟩ := hq
    have hq : q.1 = (X.posSym u, true) :=
      (Subtype.heq_iff_coe_eq (fun _ => iff_of_true q.2 rfl)).1 hu
    have h4 : HEq (where₂ X q) (X.posSym u) := (cast_heq _ _).trans (heq_of_eq (congrArg Prod.fst hq))
    have h5 : q.1.2 = true := congrArg Prod.snd hq
    have := B.bper A B' ι ho hr hs hi (where₂ X q) ⟨u, h4⟩ sF μ 𝓕 hv μN 𝓕N h1 h2 h3 s hs' φ F hφ
    show (if q.1.2 then X.Bper A B' ι (where₂ X q) sF φ F else 0) = _
    rw [if_pos h5]
    exact this

def cutAll {X : ThetaX D} {Ap : TH.ProvA} (H : AllTied D X Ap) : AllTied D (cut X) Ap where
  T := cutT H.T
  sm := H.sm
  ty := H.ty
  W := cutW H.W
  unr := H.unr
  kf := { H.kf with }
  phiUp := H.phiUp
  B := cutB H.B
  real := H.real
  prov := H.prov

theorem cut_empty (X : ThetaX D) (t j : ℕ) (hj : j < D.R.m) :
    IsEmpty ((cut X).Pos ((cut X).Xs t j) ((cut X).Ys t j) ((cut X).iXYs t j)) :=
  ⟨fun q => emb_ne X t j hj q.2⟩

end GlobalTheory.BesselGap

end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open scoped TensorProduct ContDiff

namespace GlobalTheory.WeilTieCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hHom_add_left (V W : HSp D) (x x' y : WA V W) : hHom V W (x + x') y = hHom V W x y + hHom V W x' y := by
  unfold hHom
  split_ifs <;> simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem hHom_add_right (V W : HSp D) (x y y' : WA V W) : hHom V W x (y + y') = hHom V W x y + hHom V W x y' := by
  unfold hHom
  split_ifs <;> simp [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem symplH_add_left (V W : HSp D) (x x' y : WA V W) :
    symplH V W (x + x') y = symplH V W x y + symplH V W x' y := by
  unfold symplH sympl
  rw [hHom_add_right, mul_add, map_add, mul_add]

theorem symplH_add_right (V W : HSp D) (x y y' : WA V W) :
    symplH V W x (y + y') = symplH V W x y + symplH V W x y' := by
  unfold symplH sympl
  rw [hHom_add_left, mul_add, map_add, mul_add]

theorem heis_heis (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (w w' : WA V W) (f : WA V W → ℂ) :
    Heisenberg₂ ψ V W w (Heisenberg₂ ψ V W w' f) = ψ (symplH V W w w') • Heisenberg₂ ψ V W (w + w') f := by
  funext x
  simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul, symplH_add_left, symplH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heis_quasi (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (w₀ : WA V W) (f : WA V W → ℂ)
    (hf : ∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) (γ) (w : WA V W) :
    Heisenberg₂ ψ V W w₀ f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * Heisenberg₂ ψ V W w₀ f w := by
  simp only [Heisenberg₂]
  rw [add_assoc, hf, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    symplH_add_left, symplH_add_right]
  congr 2
  ring

theorem symplH_transpose (V W : HSp D) (hne : V.rank ≠ W.rank) (x y : WA V W) :
    symplH W V x.transpose y.transpose = symplH V W x y := by
  unfold symplH sympl
  rw [hHom_transpose V W hne]

theorem isThetaFun_transpose (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (hne : V.rank ≠ W.rank) (f : WA V W → ℂ)
    (hf : IsThetaFun ψ V W f) : IsThetaFun ψ W V (fun y : WA W V => f y.transpose) := by
  have ct : Continuous fun y : WA W V => (y.transpose : WA V W) := continuous_id.matrix_transpose
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp ct, fun k L hL h0 w => ?_⟩
  · have e : (ratW W V γ).transpose = ratW V W γ.transpose := rfl
    have := hf.quasi γ.transpose w.transpose
    rw [← e, symplH_transpose W V hne.symm] at this
    simpa [Matrix.transpose_add] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    let τ : WA W V →+ WA V W := (Matrix.transposeAddEquiv _ _ _).toAddMonoidHom
    refine ⟨U.comap τ, hU.preimage ct, fun u hu h0 => ?_⟩
    have h1 : (u.transpose : WA V W).map (infPart D) = 0 := by
      ext i j; exact congrFun (congrFun h0 j) i
    funext y
    have := congrFun (hfix u.transpose hu h1) y.transpose
    simp only [Heisenberg₂] at this ⊢
    rw [symplH_transpose W V hne.symm] at this
    simpa [Matrix.transpose_add] using this
  · let τ : WA W V →+ WA V W := (Matrix.transposeAddEquiv _ _ _).toAddMonoidHom
    have := hf.smooth k (τ.comp L) (ct.comp hL) (fun t => by
      ext i j; exact congrFun (congrFun (h0 t) j) i) w.transpose
    exact this

variable {X : ThetaX D} {T : ThetaTied D X}

def noFact (X : ThetaX D) : ThetaX D := { X with fact := fun _ _ => ∅ }

def allTied_noFact {A : TH.ProvA} (h : AllTied D X A) : AllTied D (noFact X) A where
  T := { h.T with }
  sm := h.sm
  ty := { h.ty with }
  W := { h.W with om_tw := { h.W.om_tw with } }
  unr := h.unr
  kf := { h.kf with }
  phiUp := h.phiUp
  B := { h.B with }
  real := h.real
  prov := h.prov

open Classical in

def junkLift (T : ThetaTied D X) (J : ∀ V W, X.Sch V W →ₗ[ℂ] X.cusp V →ₗ[ℂ] X.AF W) : ThetaX D :=
  { X with th := fun V W χ χ' =>
      if ResEta D (T.eChr χ) V.rank ∧ ResEta D (T.eChr χ') W.rank then X.th V W χ χ' else J V W }

def allTied_junkLift {A : TH.ProvA} (h : AllTied D X A) (J : ∀ V W, X.Sch V W →ₗ[ℂ] X.cusp V →ₗ[ℂ] X.AF W) :
    AllTied D (junkLift h.T J) A where
  T := { h.T with }
  sm := h.sm
  ty := { h.ty with }
  W := { h.W with
    om_tw := { h.W.om_tw with }
    th := fun V W χ χ' hne h1 h2 hs μ 𝓕 hv Φ F g => by
      have e : (junkLift h.T J).th V W χ χ' = X.th V W χ χ' := if_pos ⟨h1, h2⟩
      rw [e]
      exact h.W.th V W χ χ' hne h1 h2 hs μ 𝓕 hv Φ F g }
  unr := h.unr
  kf := { h.kf with }
  phiUp := h.phiUp
  B := { h.B with }
  real := h.real
  prov := h.prov

end GlobalTheory.WeilTieCheck

end
end

