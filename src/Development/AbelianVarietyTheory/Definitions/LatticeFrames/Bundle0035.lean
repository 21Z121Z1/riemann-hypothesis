import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFramedAdapted
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

section Frame

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {A : Formalism.BasicNotions.TH.HSp D}

theorem besVec_ne_zero (B : SBes X h u ψ A) : B.d.i₀ *ᵥ vecB B.o B.ζ ≠ 0 := fun h0 => by
  apply B.line.2
  have e : B.L.gram *ᵥ B.ζ = (B.o.iBᴴ * (B.d.i₀ᴴ * (D.sp.Y 0).gram)) *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) := by
    rw [← B.o.isoB, ← B.d.iso]
    simp only [vecB, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, h0]; simp

theorem besScale_unique (B : SBes X h u ψ A) {μ μ' : D.host.E}
    (h₁ : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))
    (h₂ : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ' * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) : μ = μ' := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 (besVec_ne_zero B)
  have hz : X.ιE (X.zR u (Fin.cast (rank_eq X h) k)) ≠ 0 := fun h0 => hk (by rw [h₁, h0, mul_zero]; rfl)
  exact mul_right_cancel₀ hz ((h₁ k).symm.trans (h₂ k))

theorem Framed.lines {B : SBes X h u ψ A} (hB : Framed B) (a : Fin D.R.rS) :
    ∃ s s' : D.host.E, (∀ k, B.d.e k a = s * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧
      ∀ k, B.d.e' k a = s' * X.ιE (X.fR a (Fin.cast (rank_eq X h) k)) := by
  obtain ⟨μ, lam, -, -, -, he, he'⟩ := hB
  exact ⟨_, _, fun k => he k a, fun k => he' k a⟩

theorem Framed.e'_eq {A' : Formalism.BasicNotions.TH.HSp D} {u' : D.what₂.Word} {B : SBes X h u ψ A} {B' : SBes X h u' ψ A'}
    (hB : Framed B) (hB' : Framed B') (e : B'.d.e = B.d.e) : B'.d.e' = B.d.e' := by
  obtain ⟨μ, lam, -, -, -, he, he'⟩ := hB
  obtain ⟨μ', lam', -, -, -, ge, ge'⟩ := hB'
  ext k a
  have hne : ∃ r, B.d.e r a ≠ 0 := by
    by_contra hc
    push Not at hc
    have := congrFun (congrFun B.d.e'e a) a
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simp [hc] at this
  obtain ⟨r, hr⟩ := hne
  have hz : X.ιE (X.eR a (Fin.cast (rank_eq X h) r)) ≠ 0 := fun h0 => hr (by rw [he, h0, mul_zero])
  have hs := mul_right_cancel₀ hz ((ge r a).symm.trans ((congrFun (congrFun e r) a).trans (he r a)))
  rw [ge', he', hs]

theorem Framed.shear_eq_zero {B B' : SBes X h u ψ A} (hB : Framed B) (hB' : Framed B')
    {c : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (e : B'.d.e = B.d.e) (e' : B'.d.e' = B.d.e' + B.d.e * c) : c = 0 := by
  have e1 : B.d.e * c = 0 := by simpa [hB.e'_eq hB' e] using e'
  have := congrArg (fun x => B.d.e'ᴴ * (D.sp.Y 0).gram * x) e1
  simpa only [← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, Matrix.mul_zero] using this

theorem exists_framed_adapted (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : IdE X)
    (hψ : IsStdChar D ψ (-1)) (μ : D.host.E) (hμ : μ ≠ 0) (vA : Vol (D.sp.X 0)) :
    ∃ B : SBes X h u ψ (D.sp.X 0), Framed B ∧ B.Adapted tr.wt ∧
      ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k)) := by
  obtain ⟨lam, hl, H⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B, ha, -, hz, he, he'⟩ := H μ vA hμ
  exact ⟨B, ⟨μ, lam, hμ, hl, hz, he, he'⟩, ha, hz⟩

end Frame

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def InPlace : Prop := Placed f B ∧ Framed B

variable {f B}

theorem Placed.adapted (h : Placed f B) : B.Adapted (W.S.tr u).wt := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb⟩ := h
  exact hb.adapted

theorem Placed.levTrace (h : Placed f B) : LevTrace f B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb⟩ := h
  exact hb.trace

theorem InPlace.common (h : InPlace f B) :
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
      (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg),
      f.c.Is ∧ v.Is ∧ VTie f v ∧ ShapeOff v o ∧ GPin G ∧ GRead f G pl ∧ BotTie f B v o G ∧
      ∃ μ lam s : D.host.E, μ ≠ 0 ∧ μ * lam = -D.host.xi0 ^ (D.R.m / 2) ∧
        (s = (W.S.X.B.g : D.host.E) ∨ s = -(W.S.X.B.g : D.host.E)) ∧
        (∀ j hj, v.τ j hj *ᵥ o.ζ₀ = lam • (f.c.bes j 0 hj).ζ) ∧
        (∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
        (∀ r (a : Fin D.R.rS), B.d.e r a =
          μ * s ^ (D.R.rS - (a : ℕ)) * W.S.X.ιE (W.S.X.eR a (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
        ∀ r (a : Fin D.R.rS), B.d.e' r a =
          (star (μ * s ^ (D.R.rS - (a : ℕ))))⁻¹ * W.S.X.ιE (W.S.X.fR a (Fin.cast (rank_eq W.S.X W.Q.instEq) r)) := by
  obtain ⟨⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, hb⟩, μ, s, hμ, hs, hz, he, he'⟩ := h
  obtain ⟨μ', lam, n1, n2, n3⟩ := hb.norm
  obtain rfl : μ = μ' := besScale_unique B hz n2
  exact ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, hb, μ, lam, s, hμ, n1, hs, n3, hz, he, he'⟩

variable (f B)

theorem shift_tOf (a₀ a : GA D (D.sp.X 0)) :
    (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * tOf f B a₀ a =
      embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) := by
  unfold tOf
  rw [mul_assoc, mul_inv_cancel_left]

theorem tOf_eq_iff (a₀ a : GA D (D.sp.X 0)) (t : GA D (D.sp.Y 0)) :
    tOf f B a₀ a = t ↔ embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) =
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * t := by
  rw [← shift_tOf, mul_right_inj]

example : tOf f B 1 1 = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * (show GA D (D.sp.Y 0) from f.g.b 0) := by
  unfold tOf
  rw [mul_one, map_one, mul_one]

example (d : BotDat W u) {z : GA D (D.sp.Y 0)} (hp : d.Pin z) (hb : (show GA D (D.sp.Y 0) from f.g.b 0) = d.b) :
    tOf f d.B d.a₀ d.a = z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k := by
  rw [tOf_eq_iff, hb]; exact hp.eq

example (f' : FamCh W u) (B' : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (c : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hc : c ≠ 0) (e : B'.d.e = B.d.e) (e' : B'.d.e' = B.d.e' + B.d.e * c) (h : InPlace f B) : ¬ InPlace f' B' :=
  fun h' => hc (h.2.shear_eq_zero h'.2 e e')

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsStage
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def comL (L : LevCh D Unit) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (P : LevelP L.Pg D.R.r ℂ) : Com D :=
  ⟨θ, ψ, L.mu (), L.eta, L.Pg, P, L.chi⟩

theorem mem_S {L : LevCh D Unit} (hL : L.Is ()) (θ ψ P) (k : Fin 2) (Q : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ (comL L θ ψ P).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k Q hk with h1 | ⟨Q', h1, hc⟩
  · exact ⟨Q, (hL.Pg Q).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨Q', (hL.Pg Q').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ Q'.asIdeal ↔ algebraMap _ _ x ∈ Q.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

theorem comL_is {L : LevCh D Unit} (hL : L.Is ()) {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (P : LevelP L.Pg D.R.r ℂ) : (comL L θ ψ P).Is := by
  have hμ : ∀ j : Fin D.R.m, ChrEq (L.mu () ((j : ℕ) + 1)) (L.C.mu0 j) := fun j => by
    have := GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 j) (hL.xi ())
    rw [hL.xi_base, mul_one] at this
    exact this
  refine ⟨hθ, hψ, ⟨hL.eta.1, GlobalTheory.Mem.TupChar.unramEverywhere hL.eta L.C.isEta.unr, GlobalTheory.HeckeCharacterRestriction.resEta_eta hL, fun τ => ?_,
    fun j hj => ?_⟩, fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hL.chi j⟩, ?_⟩
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL () ⟨i, by omega⟩, GlobalTheory.HeckeCharacterRestriction.resEta_mu hL () ⟨i, by omega⟩⟩
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (L.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((L.C.isMu0 j).unr w fun k hk => hw (mem_S hL θ ψ P k w hk))
  · exact GlobalTheory.CentralShift.exists_idemSum _ fun Q hQ Q' hQ' => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hQ) (Or.inl hQ')

theorem pg_nonempty {L : LevCh D Unit} (hL : L.Is ()) : L.Pg.Nonempty := by
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty ((L.C.P.pb 0).asIdeal.primesOver (𝓞 D.host.E)))
  have hne : W ≠ ⊥ := by
    rintro rfl
    have := hWQ.over
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)] at this
    exact (L.C.P.pb 0).ne_bot this
  exact ⟨⟨W, hW, hne⟩, (hL.Pg _).2 ⟨0, HeightOneSpectrum.ext hWQ.over.symm⟩⟩

theorem exists_com (C : Formalism.L2.Host.CharFrame D) :
    ∃ c : Com D, c.Pg.Nonempty ∧ ∀ P : LevelP c.Pg D.R.r ℂ, Com.Is { c with P := P } := by
  obtain ⟨L, -, hL⟩ := GlobalTheory.LevelChoices.exists_levCh_unit D C
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  exact ⟨comL L θ ψ L.triv, pg_nonempty hL, fun P => comL_is hL hθ hψ P⟩

theorem exists_haar (V : HSp D) :
    ∃ (ν : Measure (GA D V)) (𝓖 : Set (GA D V)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓖 ν := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓖, h⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V Measure.haar inferInstance
  exact ⟨Measure.haar, 𝓖, inferInstance, h⟩

theorem exists_stage (hN : GlobalTheory.Published.DiscreteSeriesExists) (c : Com D) (j : ℕ) (hj : j ≤ D.R.m) :
    ∃ s : PiLocalization₂ D, s.V = D.sp.Y j ∧ s.Is c j := by
  obtain ⟨M⟩ := GlobalTheory.Published.dsExists_of_discreteSeriesExists hN D _ _ (D.sp.Y_sig j) (GlobalTheory.ChainModels.goodPar_parB D j hj)
  obtain ⟨β, n, hβ⟩ := GlobalTheory.T.exists_selfDual_adelic_frame_level_one D (D.sp.Y j) _ (GlobalTheory.LevelChoices.coe_crdLat _) (GlobalTheory.LevelChoices.dualL_crdLat _)
  rw [one_pow] at hβ
  obtain ⟨ν, fd, hν, hfd⟩ := exists_haar (D := D) (D.sp.Y j)
  have hr : D.R.r ≤ (D.sp.Y j).rank := by rw [D.sp.Y_rank j hj]; exact Nat.le_add_right _ _
  refine ⟨⟨D.sp.Y j, _, M, _, β, Lev.datY _ D.R.r D.R.t j hr c.Pg ∅ c.P c.chi (fun _ => 1) Lev.Frm.B, ν, fd⟩, rfl,
    D.sp.Y_rank j hj, D.sp.Y_sig j, D.Y_sigval j hj, rfl, GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hβ, hβ.1,
    ⟨1, hβ, fun P _ h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h))⟩, ⟨hr, _, rfl⟩, hν, hfd⟩

theorem exists_reach (hN : GlobalTheory.Published.DiscreteSeriesExists) (c : Com D)
    (hstep : ∀ k < D.R.m, ∀ s s' : PiLocalization₂ D, s.Is c k → s'.Is c (k + 1) → ∃ p : Step c s s', p.Is (k + 1))
    (s₀ : PiLocalization₂ D) (h₀ : s₀.Is c 0) : ∀ k ≤ D.R.m, ∃ s : PiLocalization₂ D, s.Is c k ∧ ∃ Θ, Reach c s₀ k s Θ := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨s₀, h₀, _, Reach.zero⟩
  | succ k ih =>
    intro hk
    obtain ⟨s, hs, Θ, hΘ⟩ := ih (by omega)
    obtain ⟨s', -, hs'⟩ := exists_stage hN c (k + 1) hk
    obtain ⟨p, hp⟩ := hstep k (by omega) s s' hs hs'
    exact ⟨s', hs', _, hΘ.step hs' p hp⟩

theorem it_ne_zero {c : Com D} {s s' : PiLocalization₂ D} {p : Step c s s'} {j : ℕ} (h : p.Is j) : p.It ≠ 0 := h.it.ne

theorem chainPar_two (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (w) :
    (chainPar c B 2 w).card = (B w).card + 2 * D.R.t := by
  simp only [chainPar_succ, stepPar, Multiset.card_add, Multiset.card_map, GlobalTheory.LFun.seg, Finset.card_val, Finset.card_range]
  show (B w).card + _ + _ = _
  ring

end GlobalTheory.ChainOnto.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (a : GeoAll W u)

structure Cst where
  ε : ℕ → a.ι → 𝓀[a.k]ˣ
  op : ∀ j, BiOp (D.sp.X j) (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1))
  r : ℕ → a.ι → ℝ
  e : ℕ → a.ι → ℤ
  cG : ℕ → ℂ
  sc : W.P.T → ℕ → ℂ

variable {a} (k : Cst a)

abbrev Cst.v : VCom (commOf (pk W) u a.g) := (a.v.withT (a.o.S k.ε) k.op).withCG k.cG

variable {row : ∀ t, RowCh (pk W) (lvP W) u a.g t} {col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))}

structure ColOut (w₀ w : ∀ t, VTup ((a.fam row col).t t))
    (F : ∀ t, GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) : Prop where
  ok : (a.fam row col).ColOK
  pins : ∀ t, (F t).Pins (w₀ t)
  same : ∀ t, (w t).Q = (w₀ t).Q ∧ (w t).eQ = (w₀ t).eQ ∧ (w t).eQT = (w₀ t).eQT ∧ (w t).cQ = (w₀ t).cQ ∧ (w t).FY = (w₀ t).FY ∧
    (w t).FT = (w₀ t).FT
  laws : ∀ t, QLaw a.v (w t) ∧ QLast a.v (w t) ∧ QFin a.v (w t)
  lev : ∀ t, QLev (a.fam row col) (F t)
  vec : ∀ t, QVec (a.fam row col) (w₀ t)
  FY : ∀ t j f, f ∈ (w₀ t).FY j ↔ ∀ i, ((F t).Q i).Typed j f
  FT : ∀ t f, f ∈ (w₀ t).FT
  FX : ∀ t j, j + 2 ≤ D.R.m → ∀ ψ ∈ (col t).Ram j, ∀ α y, (col t).rd j α ψ y ∈ (w t).FX j α
  atQ : ∀ t j, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w₀ t).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w₀ t).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w t).dQ j α γ)
  e : ∀ t j α, (col t).e j α = ((w t).ε j α).mapDomain (· * a.g.b j) ∧
    ∀ g ∈ ((w t).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ (w₀ t).Q)
  eT : ∀ t n h β, (col t).eT n h β = ((w t).εT n h β).mapDomain (· * a.g.bT) ∧
    ∀ g ∈ ((w t).εT n h β).support, g ∈ GlobalTheory.FinPl.grpAt D.sp.X' (· ∈ (w₀ t).Q)
  dd : ∀ t j, j < D.R.m → ∀ α γ f, IsThetaFunO (pk W).ψ _ _ f → comb (pk W).ψ _ _ ((col t).dd j α γ) f =
    comb (pk W).ψ _ _ ((w t).dQ j α γ) (comb (pk W).ψ _ _ (a.v.dG j) (comb (pk W).ψ _ _ (a.v.dT j) f))
  read : ∀ t, ∃ S₀, ReadS a.o ((a.fam row col).t t) k.ε S₀
  sc : ∀ t, (w t).sc = k.sc t
  cT : ∀ t j ρ h, (w t).cT j = a.o.mono (k.r j) (k.e j) ((row t).sBF j ρ h).χW
  cv : ∀ t, CVEq k.v (w t)
  cK : ∀ t j, j < D.R.m → UnitRatio (qPrime W t) ((col t).cK j) ((col W.P.A3.A.μ0).cK j)
  cP : ∀ t, UnitRatio (qPrime W t) (col t).cP (col W.P.A3.A.μ0).cP
  zero : ChartZero (a.fam row col)

end Gen

section True

open GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

def LevTrue (W : RealPack ex) : Prop :=
  GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg ∧ (∀ PP, PP ∈ (pk W).Pg ↔ PP ∈ (B.primes X).vGs) ∧ ∀ t, (pk W).xiH t = I.xi (W.P.I.tup t)

structure AllTrue (W : RealPack ex) : Prop where
  pk : PkHyp W
  tr : TrueW W
  tq : TrueQ W
  tw : GlobalTheory.AdForm.TwStd W
  lev : LevTrue W
  rc : Nonempty (RealRec W.Q)

end True

end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZero

open GlobalTheory.ChainOnto (Com)

variable {D : D7}

section Common

variable {c : Comm D} {v : VCom c}

def Red (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1

structure LocAt (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)) : Prop where
  idem : Formalism.L2.NTheta.IsIdemAt G.q.e PP
  under : G.q.v = PP.under (𝓞 D.host.F)
  frame : ∀ a (ha : 0 + a = G.s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) 0 ≃ Fin (c.V 0).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit G.q) (c.V 0) b β
      (((G.FY 0 a ha).β * ((G.S.T (Fin D.R.t)).bas 0 a ha).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) 0 a ha (e.symm i))

structure Bot (cm : Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) : Prop where
  com : cm.Is
  psi : cm.ψ = c.ψ
  mem : st.st.Is cm 0
  fin : b ∈ GfC (c.V 0)
  typ : IsTypePlaces cm.Pg
  loc : ∀ PP : cm.Pg, LocAt (G PP) PP.1 b st.β
  grp : ∀ g : ∀ PP : cm.Pg, GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1), g ∈ cm.P.H ↔ ∀ PP, ∃ x, Red (G PP) PP.1 x (g PP)
  chr : ∀ (g : cm.P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, Red (G PP) PP.1 (x PP) (g.1 PP)) →
    cm.P.chi g = ∏ PP, (G PP).S.P.lam (x PP)

end Common

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

abbrev datZero (W : RealPack ex) : Formalism.L2.DIV.LevDat D.host.E ℂ (Yc D 0).rank :=
  W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)

def stZero (W : RealPack ex) : StAt (Yc D 0) where
  par := (GlobalTheory.BaseChain.stageY W 0).par
  M := (GlobalTheory.BaseChain.stageY W 0).M
  Λ := (pk W).ΛY 0
  β := (pk W).βY 0
  L := datZero W
  ν := (GlobalTheory.BaseChain.stageY W 0).ν
  fd := (GlobalTheory.BaseChain.stageY W 0).fd

variable {W : RealPack ex} {u : D.what₂.Word}

structure PlacedBy (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg) : Prop where
  cis : f.c.Is
  vis : v.Is
  tie : VTie f v
  shape : ShapeOff v o
  pin : GPin G
  read : GRead f G pl
  bot : BotTie f B v o G

set_option maxHeartbeats 1000000 in

def frAt (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) :
    GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) :=
  finE (D.sp.Y 0) (tOf f B a₀ a) * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0)

set_option maxHeartbeats 1000000 in

def StabAt (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) : Prop :=
  ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (frAt f B a₀ a)) ↔
    ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset)

end GlobalTheory.LevZero

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def PrimTop {c : Comm D} (tP : Finset (GlobalTheory.FinPl.Pl D)) (ζ₀ : Fin c.Lz.rank → D.host.E) : Prop :=
  ∀ p, p ∉ tP → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = p),
    a • ratV (vecB (c.oT D.R.m rfl) ζ₀) ∈ GlobalTheory.FinPl.latV (c.X D.R.m) (c.x D.R.m).L (· = p) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = p)

def PlacedP : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg),
    f.c.Is ∧ v.Is ∧ VTie f v ∧ ShapeOff v o ∧ GPin G ∧ GRead f G pl ∧ BotTie f B v o G ∧ PrimTop (c := f.c) v.tP o.ζ₀

theorem PlacedP.placed (h : PlacedP f B) : Placed f B := by
  obtain ⟨k, a1, a2, a3, a4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  exact ⟨k, a1, a2, a3, a4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, h7⟩

end GlobalTheory.MiTop

end
end

