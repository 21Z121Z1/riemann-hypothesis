import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0071
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0083
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntegralOfMemIntAE
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFifth
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CoverVal

theorem perFr_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r} (h : SameSp X' X)
    (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X' x v τ i = perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X
  cases X'
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem sameSp_of {D : D7} {W : HSp D} {r : ℕ} {hr : W.rank = r} {X' X : Data D.host.E r} (h' : IsMod W hr X')
    (h : IsMod W hr X) (hp : X'.p0 = X.p0) : SameSp X' X :=
  ⟨Finset.ext fun τ => (h'.psi τ).trans (h.psi τ).symm, h'.model.1.trans h.model.1.symm, hp,
    h'.model.2.trans h.model.2.symm, h'.kap.trans h.kap.symm⟩

theorem realM_mul {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (γ k : GA D W)
    (δ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (hδ : ∀ (τ : D.host.E →+* ℂ) th, IsInfEmb τ th → archM W th γ = δ.map τ) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) :
    realM θ (Formalism.L2.Theta.mt W (γ * k)) τ = δ.map τ * realM θ (Formalism.L2.Theta.mt W k) τ := by
  have h1 := hδ τ (θ hτ.choose) (by have h := hθ hτ.choose; rwa [← hτ.choose_spec] at h)
  rw [realM, realM, dif_pos hτ, dif_pos hτ, ← h1]
  change archM W _ (γ * k) = _ * archM W _ k
  rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]

open CategoryTheory MonObj in

theorem marked_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

theorem move_congr {A : Type} [CommRing A] {n N : ℕ} (p q : Matrix (Fin n) (Fin n) A) {x x' b w w' : Fin n → A}
    (h : x - q *ᵥ b = N • w) (h' : x' - p *ᵥ (q *ᵥ b) = N • w') : p *ᵥ x - x' = N • (p *ᵥ w - w') := by
  rw [smul_sub, ← h', ← Matrix.mulVec_smul, ← h, Matrix.mulVec_sub, sub_sub_sub_cancel_right]

theorem point_eq {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (h1 : 1 ≤ r) (hA : l.A = 1) {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (Wt : UW U) (j : U.Comp) (x' : Frame (U.X j).Ψ r) (γ k : GA D W) (hγ : γ ∈ GQ W) (hm' : IsMod W hr (U.X j))
    (hL' : latR hr (latG W (γ * k)) = (U.X j).Λ) (hx' : x' = frMove θ W hr (U.X j) (γ * k) fun τ => x₀ τ.1)
    (hon : IsONFr (U.X j) x') (hk' : MarkAd l W hr ι (γ * k) (Wt.mark j))
    (X : Data D.host.E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (hm : IsMod W hr X) (hp : X.p0 = Dw.q) (hs : IsSympl X bas)
    (hi : IdxIs c σ X idx e) (hL : latR hr (latG W k) = X.Λ) (hmk : IsMark l X.Λ mk) (hk : MarkAd l W hr ι k mk) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y : FrPt Xo c ℂ) (A : AnFib X bas idx e (frMove θ W hr X k fun τ => x₀ τ.1) X.Λ y), A.Marked mk →
      ∃ h : x' ∈ (U.X j).dom, y.x = (U.un j ⟨x', h⟩).x := by
  let _ : Algebra c.F ℂ := σ.toAlgebra
  intro y A hA'
  subst hr
  obtain rfl : g = Wt.g := Fin.equiv_iff_eq.1 ⟨e.trans Wt.e.symm⟩
  obtain ⟨π, rfl⟩ : ∃ π : Equiv.Perm (Fin Wt.g), e = π.trans Wt.e :=
    ⟨e.trans Wt.e.symm, Equiv.ext fun a => (Wt.e.apply_symm_apply _).symm⟩
  obtain ⟨idx, rfl⟩ : ∃ idx' : Fin Wt.g ≃ X.Ψ × Fin W.rank, idx = π.trans idx' :=
    ⟨π.symm.trans idx, Equiv.ext fun a => congrArg idx (π.symm_apply_apply a).symm⟩
  have hsp : SameSp (U.X j) X := sameSp_of hm' hm ((hU.2.1 j).1.trans hp.symm)
  obtain ⟨-, hsd, -⟩ := uw_lattice _ H Dw l Xo c σ _ U hσ hU h1 Wt j
  obtain ⟨Dc, hDc, -⟩ := exists_dic _ H Dw l c σ _ Wt.g 0 (U.X j) 0 Wt.e hσ hU.1 (hU.2.1 j).1 (hU.2.1 j).2 hsd
    ⟨fun _ => antitone_const, Even.zero⟩
  have hper := Dc.per_eq
  have hty := Dc.ty_eq
  rw [hDc] at hper hty
  obtain ⟨hd', hu', -⟩ := hx_of_isONFr _ _ _ 0 (U.X j) Dc.bas Dc.idx Dc.sympl Even.zero x' hon
  obtain ⟨A', hA'', -⟩ := uw_anFib _ H Dw l Xo c σ _ U hσ hU h1 Wt j Dc.bas Dc.idx Dc.sympl hper hty ⟨x', hd'⟩ hu'
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix W γ hγ
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hG : X.Gm = -W.gram.transpose := hm.model.1
  have hun : IsUn X δ⁻¹ := fun u v => by rw [hG, ← hδu, hri, hri]
  have hR : ∀ L : Lt D.host.E W.rank, latR rfl L = L := fun L => Submodule.map_id L
  rw [hR] at hL hL'
  have hmem : ∀ v, v ∈ X.Λ ↔ δ.1 *ᵥ v ∈ (U.X j).Λ := fun v => by
    rw [← hL, ← hL', GlobalTheory.Member.LatMove.mem_lat_iff, GlobalTheory.Member.LatMove.mem_lat_iff,
      GlobalTheory.Member.LatMove.move_iff W γ k, hδf]
  obtain ⟨hd, -, hsd', A'', -, -, hM⟩ := anFib_move _ H Dw l Xo c _ _ (U.X j) X hsp Dc.bas Dc.idx bas idx Wt.e x' _ _ A' δ⁻¹
    Dc.sympl hs hd' hsd hun
    (fun v => funext fun a => by
      obtain ⟨a, rfl⟩ := π.surjective a
      exact (hper x' v _).trans ((perFr_cast hsp _ _ _ _).trans (hi.1 _ v a).symm))
    (fun a => by
      obtain ⟨a, rfl⟩ := π.surjective a
      exact (hty _).trans (hi.2 a).symm)
  have hM' := hM _ hA''
  have e1 : mapL δ⁻¹ (U.X j).Λ = X.Λ := Submodule.ext fun v => by
    rw [Lev.mem_mapL, inv_inv, hmem]; rfl
  have e2 : lact δ⁻¹ (castFr hsp.psi x') = frMove θ W rfl X k fun τ => x₀ τ.1 := by
    funext τ
    rw [hx']
    change (δ⁻¹).1.map τ.1 * (realM θ (Formalism.L2.Theta.mt W (γ * k)) τ.1 * x₀ τ.1) =
      realM θ (Formalism.L2.Theta.mt W k) τ.1 * x₀ τ.1
    rw [realM_mul hθ W γ k δ.1 hδa τ.1 ((hm.psi _).1 τ.2), ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul,
      Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  revert A'' hd hsd'
  rw [e1, e2]
  intro hd hsd' A'' _ hM'
  refine ⟨hd', anFib_point_eq _ H Dw l Xo c hA _ _ X bas idx Wt.e _ _ _ y A'' (Cmp.anFibRen π A) hs hd hsd' mk hmk
    (marked_congr A'' hM' fun a ha => ?_) hA'⟩
  obtain ⟨w, hw, ew⟩ := hk a ha
  obtain ⟨w', hw', ew'⟩ := hk' a ha
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (δ.1 *ᵥ mk a - Wt.mark j a) ((finHom W γ).1 *ᵥ w - w') (by
    have e3 : finVec W (δ.1 *ᵥ mk a - Wt.mark j a) = finVec W (δ.1 *ᵥ mk a) - finVec W (Wt.mark j a) :=
      funext fun i => TensorProduct.tmul_sub _ _ _
    rw [e3, ← hδf]
    exact move_congr _ _ ew (GlobalTheory.Member.LatMove.fin_mul W γ k _ ▸ ew'))
  refine ⟨(δ⁻¹).1 *ᵥ u, ?_, ?_⟩
  · rw [hmem, hri, ← hL', GlobalTheory.Member.LatMove.mem_lat_iff, hu]
    exact sub_mem (GlobalTheory.Member.LatMove.move_mem W γ k w hw) hw'
  · rw [← Matrix.mulVec_smul, ← eu, Matrix.mulVec_sub, hli]
    exact (add_sub_cancel _ _).symm

theorem evR_eq_of_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (σ : c.F →+* ℂ) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (y y' : FrPt Xo c (CAt σ)) (h : y'.x = y.x) : toC (evR Xo c f y') = toC (evR Xo c f y) :=
  GlobalTheory.WeightZeroValue.evR_conj E H Dw l Xo c σ (RingEquiv.refl ℂ) f hf y y'
    (h.trans ((CategoryTheory.Category.id_comp _).symm.trans
      (congrArg (CategoryTheory.CategoryStruct.comp · y.x) (AlgebraicGeometry.Spec.map_id _).symm)))

theorem cover_value : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ c0 : ℂ, ‖c0‖ = 1 ∧ ∀ (t : Tp) (X : Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → IsSympl X bas → IdxIs O.c' (inC O.c') X idx e → latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → IsMark (O.dδ t).l₂ X.Λ mk → MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) k mk → letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra; ∀ (y₂ : FrPt (O.dδ t).Xo₂ (O.dδ t).c₂ ℂ) (A₂ : AnFib X bas idx e (frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.x₀ ((i : ℕ) + 1) O.s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (O.dδ t).Xo₂ (O.dδ t).c₂ (O.dδ t).cδ y₂ = c0 * ((R.xi (tup t) xk : Circle) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup O hO
  obtain ⟨c0, ⟨m, hm0, hm⟩, hc⟩ := hO.cxi
  refine ⟨c0, Complex.norm_eq_one_of_pow_eq_one hm hm0.ne', ?_⟩
  intro t X g bas idx e k xk mk hX hp hs hi hL hxk hmk hk y₂ A₂ hA₂
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc t
  obtain ⟨hlev, hA, -⟩ := hO.cov t
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.T.level_form_compat_base_embedding D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    (sOv_eq _ _ _) (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ t).c₂ ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ t).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ t).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := GlobalTheory.T.dictionary_component_frame_marking_uniformisation D _ _ _ _ _ _ _ (O.U₂ t) hσ hU h1 hA R.θ (Wc D i) (rank_Wc i)
    (O.dict₂ t) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt k
  obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (O.U₂ t)) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T i)
    _ Wt (O.dict₂ t k).1 (O.dict₂ t k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hs hi hL hmk hk y₂ A₂ hA₂
  obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
  obtain ⟨-, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  obtain ⟨a, ha⟩ := hrat γ' hγ'
  have hv := hval k γ' ⟨hγ', h2, h3⟩
  rw [(hO.tuple t).xi _ _ (hmul _ _ _ _ ha hxk), map_mul, (hR.lev.xi (tup t)).1.2 a, _root_.one_mul] at hv
  exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans hv)

end GlobalTheory.AdTh.CoverVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFirst
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CcEx

noncomputable section

open GlobalTheory.ClsVal.Cmp

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

def anFibBas {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
    {X : Data E r} {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw}
    {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ} (h : ∀ z w, hx X bas' idx x z w = hx X bas idx x z w)
    (A : AnFib X bas idx e x L y) : AnFib X bas' idx e x L y where
  ex := A.ex
  ex_add := A.ex_add
  ex_onto := A.ex_onto
  ex_ker := A.ex_ker
  ex_lin := A.ex_lin
  hol := A.hol
  der := A.der
  fr := A.fr
  fr_hol := A.fr_hol
  fr_ne := A.fr_ne
  fr_g := A.fr_g
  fr_0 := A.fr_0
  χ := A.χ
  χ_norm := A.χ_norm
  fr_per v hv j z hz := by rw [h, h]; exact A.fr_per v hv j z hz

theorem coord_eq {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas)
    {x : Frame X.Ψ r} (hx' : x ∈ X.dom) {p q : X.Ψ × Fin r} (h : ∀ v, per X x v p = per X x v q) : p = q := by
  obtain ⟨i, rfl⟩ := idx.surjective p
  obtain ⟨j, rfl⟩ := idx.surjective q
  have hsp := ((hx_laws E r X g bas idx 0 hs Even.zero x hx').2.2.2.2.2.2.1 ⊤ (by simp)).1
  have key : ∀ z : Fin g → ℂ, z i = z j := by
    intro z
    have hz : z ∈ Submodule.span ℝ (pv X idx x '' ((⊤ : Lt E r) : Set (Fin r → E))) := hsp ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨v, -, rfl⟩ := hz; exact h v
    | zero => rfl
    | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]
    | smul a b _ hb => simp only [Pi.smul_apply, hb]
  by_contra hne
  have hij : j ≠ i := fun e => hne (by rw [e])
  have := key (Pi.single i 1)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
  exact one_ne_zero this

variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem genReads_change (U : Unf Xo c σ r) (k : U.Comp) {g g' : ℕ}
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx' : Fin g' ≃ (U.X k).Ψ × Fin r) (e' : Fin g' ≃ Lt1 Dw)
    (hs : IsSympl (U.X k) bas) (hs' : IsSympl (U.X k) bas') (hi : IdxIs c σ (U.X k) idx e) (hi' : IdxIs c σ (U.X k) idx' e')
    (x : (U.X k).dom) (hon : IsONFr (U.X k) x.1) (ϑ' : (Fin g' → ℂ) → ℂ) (h : GenReads U k bas' idx' e' x ϑ') :
    ∃ ϑ, GenReads U k bas idx e x ϑ ∧ ∀ u : (U.X k).Ψ × Fin r → ℂ, ϑ' (u ∘ idx') = ϑ (u ∘ idx) ∧
      hx (U.X k) bas' idx' x.1 (u ∘ idx') (u ∘ idx') = hx (U.X k) bas idx x.1 (u ∘ idx) (u ∘ idx) := by
  have hg : g' = g := by simpa using Fintype.card_congr (idx'.trans idx.symm)
  subst hg
  obtain ⟨π, rfl⟩ : ∃ π : Equiv.Perm (Fin g'), e' = π.trans e := ⟨e'.trans e.symm, by ext1; simp⟩
  have hidx : idx' = π.trans idx := by
    ext1 j
    exact coord_eq idx hs x.2 fun v => (hi'.1 x.1 v j).trans (hi.1 x.1 v (π j)).symm
  subst hidx
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨A, hA⟩ := h
  have hb : ∀ z w, hx (U.X k) bas idx x.1 z w = hx (U.X k) bas' idx x.1 z w := fun z w => by
    rw [(hx_of_isONFr E r g' 0 _ bas idx hs Even.zero _ hon).2.2, (hx_of_isONFr E r g' 0 _ bas' idx hs' Even.zero _ hon).2.2]
  refine ⟨ϑ' ∘ ren π, ⟨anFibBas hb (anFibRen π A), fun j z pt h1 h2 h3 => hA j (ren π z) pt h1 h2 h3⟩, fun u => ⟨rfl, ?_⟩⟩
  rw [hb]
  exact hx_ren _ bas' idx π x.1 (u ∘ idx) (u ∘ idx)

end Gen

theorem thA_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g) (x : Frame X.Ψ r)
    (z : Fin n → Fin g → ℂ) : thA X bas idx (a • φ) x z = a * thA X bas idx φ x z := by
  simp only [thA, SW.thS, show ∀ y, (a • φ) y = a * φ y from fun _ => rfl, _root_.mul_assoc, tsum_mul_left]
  ring

theorem exists_ccIs_of_pair (hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {V W : HSp D} {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) {mu : GA D W → ℂ} (hmu : MuVal W χV mu) (hmuQ : ∀ γ ∈ GQ W, ∀ h, mu (γ * h) = mu h)
    {r : ℕ} (hr : W.rank = r) {H : Geo.Tor.Host D.host.E} (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : IsUnf U) (hr1 : 1 ≤ r) (hA : l.A = 1) {a : (D.host.E →+* ℂ) × ℕ → ℕ} (hdom : Dom a V.rank)
    {ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (hV0 : V.rank ≠ 0) (h1 : (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V) (h2 : (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W)
    (h3 : IsSelfDualC V ΛV) (h4 : IsSelfDualC W ΛW)
    (h5 : (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hmod : ∀ k, IsMod W hr (U.X k)) (hon : ∀ k, IsONFr (U.X k) (fun τ => x₀ τ.1))
    (hinv : ∀ k, IsInvOf W hr (U.X k) (fun τ => x₀ τ.1) s) {f : WO V W → ℂ}
    (hf : IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) : ∃ cc, CcIs θ V W hr U dict mu x₀ om f cc := by
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  have hw : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hw' : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  have key : ∀ k : U.Comp, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ (h : GA D W) (x : (U.X k).dom), latR hr (latG W h) = (U.X k).Λ →
      x.1 = frMove θ W hr (U.X k) h (fun τ => x₀ τ.1) → ∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ)
      (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X k) bas → IdxIs c σ (U.X k) idx e →
      ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads U k bas idx e x ϑ → ∀ w : WO V W, w.map (finPart D) = 0 →
        om (1, h) f w = a * mu h *
          cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (U.X k) bas idx x.1
            (zOf θ V W hr (U.X k) idx x.1 w b) (zOf θ V W hr (U.X k) idx x.1 w b)) *
          ∏ b, ϑ (zOf θ V W hr (U.X k) idx x.1 w b) := by
    intro k
    have hsd : SelfD (U.X k) (U.X k).Λ := (uw_lattice _ H Dw l Xo c σ _ _ hσ hU' hr1 Wt k).2.1
    obtain ⟨Dc, -, -⟩ := exists_dic _ H Dw l c σ _ Wt.g V.rank (U.X k) a Wt.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hsd hdom
    have hi : IdxIs c σ (U.X k) Dc.idx Dc.e := ⟨Dc.per_eq, Dc.ty_eq⟩
    obtain ⟨v, hv⟩ := (TensVac.vacua _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hP.even _ hw hw' _ hsd 1 _
      (Base.stdL_mem_Vset V.rank 1)).1
    obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.pow_generator_eq_const_mul_vacuum_theta hci _ H Dw l Xo c σ r U hσ hU hr1 hA k V.rank _ Dc.bas Dc.idx Dc.e hP.even
      Dc.sympl hi v hv
    obtain ⟨κ, -, hκ, hrd⟩ := GlobalTheory.T.exists_vacuum_multiplier_constant_per_lattice D ψ θ V W χV χW om hP mu hmu r _ hr (U.X k) Dc.bas Dc.idx (hmod k) Dc.sympl H hrt
      ΛV ΛW hV0 h1 h2 h3 h4 h5 hsd _ s (hon k) (hinv k) f hf v hv
    refine ⟨κ / C, ?_, fun h x hL hxe g bas idx e hs hie ϑ' hϑ' w hw0 => ?_⟩
    · obtain ⟨hd, hu, -⟩ := hx_of_isONFr _ r _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ (hon k)
      obtain ⟨⟨ϑ, hϑ⟩, hall⟩ := hC ⟨_, hd⟩ hu
      obtain ⟨t1, t2, t3⟩ := hall ϑ hϑ
      rw [norm_div, ← hκ _ hd hu ϑ C t1 t2 t3, div_self (norm_ne_zero_iff.2 hC0)]
    · obtain ⟨hon', -, hread⟩ := hrd h hL
      rw [← hxe] at hon' hread
      obtain ⟨-, hu, -⟩ := hx_of_isONFr _ r _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ hon'
      obtain ⟨ϑ, hϑ, hch⟩ := genReads_change U k Dc.bas Dc.idx Dc.e bas idx e Dc.sympl hs hi hie x hon' ϑ' hϑ'
      have t3 := ((hC x hu).2 ϑ hϑ).2.2 (zOf θ V W hr (U.X k) Dc.idx x.1 w)
      have e1 : ∏ b, ϑ' (zOf θ V W hr (U.X k) idx x.1 w b) = ∏ b, ϑ (zOf θ V W hr (U.X k) Dc.idx x.1 w b) :=
        Finset.prod_congr rfl fun b _ => (hch _).1
      have e2 : ∑ b, hx (U.X k) bas idx x.1 (zOf θ V W hr (U.X k) idx x.1 w b) (zOf θ V W hr (U.X k) idx x.1 w b) =
          ∑ b, hx (U.X k) Dc.bas Dc.idx x.1 (zOf θ V W hr (U.X k) Dc.idx x.1 w b)
            (zOf θ V W hr (U.X k) Dc.idx x.1 w b) :=
        Finset.sum_congr rfl fun b _ => (hch _).2
      rw [hread w hw0, e1, e2, t3, thA_smul']
      field_simp
  choose cc hcc hkey using key
  refine ⟨cc, hcc, fun h γ hat hx' g bas idx e hs hi ϑ hϑ w hw0 => ?_⟩
  rw [← hmuQ γ hat.1 h]
  exact hkey _ (γ * h) ⟨_, hx'⟩ hat.2.1 hat.2.2 g bas idx e hs hi ϑ hϑ w hw0

theorem exists_ccIs : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro hci D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup O hO
  have hs0 : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.theta_pair_characters_at_level D G Pl0 T0 A _ R F hC i A.μ0 hO.lift.std
  have hM := GlobalTheory.T.level_form_compat_base_embedding D G Pl0 T0 A T R F κ v₀ hC hT i O.s0 hs0
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) O.s0 := by
    rw [hs0, chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC.lev.xi_base ▸ hC.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) O.s0 = W),
      MuVal W (T.chiW ((i : ℕ) + 1) O.s0) (castDict hV (T.mu ((i : ℕ) + 1) O.s0)) ∧ ∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) O.s0) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) O.s0) h := by
    intro W hV
    subst hV
    have hu := hT.laws.muUnit _ (inR i) _ hσ
    exact ⟨hT.laws.muVal _ (inR i) _ hσ, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl)⟩
  obtain ⟨hmu, hmuQ⟩ := hcast _ O.hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (O.dict 1).1
  exact exists_ccIs_of_pair hci hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt _ hσ (hT.laws.unf _ (inR i) _ hσ) hr1
    hT.laws.pins.2.1.2 hdom hV0 h1 h2 h3 h4 h5 _ _ (fun k => (hM k).1) (fun k => (hM k).2.1) (fun k => (hM k).2.2.1)
    (hC.thP.vP i A.μ0).1 _

end

end GlobalTheory.AdTh.CcEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFinPartInCompactBoundedDenominator
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.BoundedDen

theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → Af D.host.F ⊗[D.host.F] D.host.E) = fun z => (e z).2 := by
    funext z; exact ((he z).2).symm
  rw [this]
  exact continuous_snd.comp hc

set_option maxHeartbeats 1000000 in

theorem bounded_den : ∀ (D : D7) (K : Set (AE D)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ k ∈ K, ∀ x : D.host.E,
    finPart D (incA D x) = finPart D k → IsIntegral ℤ ((L : D.host.E) * x) := by
  intro D K hK
  let U : AddSubgroup (AE D) := (intAE D).comap (finPart D).toAddMonoidHom
  have hU : IsOpen (U : Set (AE D)) :=
    (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_finPart D)
  obtain ⟨n, hn⟩ := GlobalTheory.CondBound.exists_small D K hK U hU
  refine ⟨n.factorial, Nat.factorial_pos n, fun k hk x hx => ?_⟩
  have h := hn k hk
  have h2 : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) ∈ intAE D := by
    have e : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) =
        finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * k) := by
      rw [map_mul (incA D), map_mul (finPart D), map_mul (finPart D), hx, GlobalTheory.CondBound.finPart_r]
    rw [e]; exact h
  obtain ⟨y, hy⟩ := GlobalTheory.FinalJoin.CondTest.integral_of_mem_intAE h2
  have e2 : (((n.factorial : ℕ) : D.host.E) * x) = (y : D.host.E) := hy.symm
  rw [e2]
  exact NumberField.RingOfIntegers.isIntegral_coe y

end GlobalTheory.BoundedDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformTransportedWeilContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_transportedWeil_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ w, Continuous fun p => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) w := by
  first | exact @GlobalTheory.ThetaTransportCont.thetaTr_om_continuous | exact GlobalTheory.ThetaTransportCont.thetaTr_om_continuous | (intros; apply GlobalTheory.ThetaTransportCont.thetaTr_om_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedArchHeisenbergDirectionsContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_archHeisenbergDirections_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) D.host.E)
    (JB : Matrix (Fin n) (Fin n) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)),
    (∀ p w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      om p (co.rho ψ w φ) = co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p w) (om p φ)) →
    ∃ M : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
        GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) → ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F (M p h)) φ) =
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  first | exact @GlobalTheory.ArchTransportHost.archDir_transport_host | exact GlobalTheory.ArchTransportHost.archDir_transport_host | (intros; apply GlobalTheory.ArchTransportHost.archDir_transport_host <;> assumption)
end

