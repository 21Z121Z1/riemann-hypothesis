import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivCoreUpPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreTiesOfHyp
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.BigOn.Inhab

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem level_of_is {T : Core D} (hT : LawsM T) {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) (hO : T.pb = Lc.C.P.pb) :
    T.Q.l.Mb = ∏ PP ∈ Lc.Pg, PP.asIdeal := by
  have hprod := T.Q.l.prod
  refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ _ fun PP => ?_
  · rw [hT.pins.2.1.1] at hprod
    exact (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (T.Q.l.Mb * _)).of_mul_left
  · rw [hL.Pg, hT.half.2, GlobalTheory.CoverHalf.prod_map_le_iff, hO]
    rfl

theorem exists_half_of_is {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) {p : ℕ} (hp : p = D.host.pde ∨ p = D.host.pde') :
    ∃ P : HeightOneSpectrum (𝓞 D.host.K), (p : 𝓞 D.host.K) ∈ P.asIdeal ∧ ∀ t, ∀ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal →
      P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  obtain ⟨P, hP⟩ := hL.Q_de p hp
  by_cases h : ∃ t, ∃ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal
  · obtain ⟨t, PP, h1, h2⟩ := h
    refine ⟨P, ?_, fun t PP h1 h2 => ?_⟩
    · rw [← hP t PP h1 h2]
      change algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (p : 𝓞 D.host.K) ∈ PP.asIdeal
      rwa [map_natCast]
    · rw [← hP t PP h1 h2]
      exact Ideal.map_comap_le
  · have hpp : p.Prime := by
      rcases hp with rfl | rfl
      exacts [D.host.pde_prime, D.host.pde'_prime]
    obtain ⟨P', hP'⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hpp
    exact ⟨P', hP', fun t PP h1 h2 => absurd ⟨t, PP, h1, h2⟩ h⟩

theorem ownAt_special (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ownAt D v = D.host.pde ∨ ownAt D v = D.host.pde' := by
  unfold ownAt
  split_ifs
  exacts [Or.inr rfl, Or.inl rfl]

theorem oneHalf_of_is {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {μ0 : T0}
    (hL : R.toLevCh.Is μ0) : ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v,
      ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧ ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
        (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  classical
  choose P h1 h2 using fun (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde') => exists_half_of_is hL hp
  refine ⟨fun p => if hp : p = D.host.pde ∨ p = D.host.pde' then P p hp else R.C.P.pb 0, fun v => ?_⟩
  simp only [dif_pos (ownAt_special v)]
  refine ⟨h1 _ _, fun PP hPP => ?_⟩
  have h3 := Finset.mem_filter.1 hPP
  exact h2 _ _ _ PP h3.1 h3.2

theorem level_and_oneHalf (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (μ0 : T0) (hL : R.toLevCh.Is μ0)
    (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) :
    J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧
      ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v ∈ R.twPl, ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧
        ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
          (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal :=
  ⟨level_of_is hc.toLawsM hL hO, (oneHalf_of_is R hL).imp fun _ h v _ => h v⟩

theorem coreTies_of_is {L : SizeData₂ D} {EX : ErrX D} {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {μ0 : T0}
    (hL : R.toLevCh.Is μ0) (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) (hcan : J.Q.Canon)
    (hr : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) (hE : HalfEX J.toCore EX) (h₁ : FieldOK0 D D.host.pde)
    (h₂ : FieldOK0 D D.host.pde') (hs : FieldSmall D L) (hd : ∀ x, ((R.C.del.1 x : ℂˣ) : ℂ) ∈ FO D)
    (hd' : ∀ x, ((R.C.del'.1 x : ℂˣ) : ℂ) ∈ FO D) : CoreTies L EX J R :=
  ⟨hc, hcan, hr, hE, h₁, h₂, hs, (level_and_oneHalf J R μ0 hL hO hc).1, (level_and_oneHalf J R μ0 hL hO hc).2, hd, hd'⟩

def IsParametersCompatibleWithCharFrame (L : SizeData₂ D) (EX : ErrX D) (J : CoreJ D) (C : Formalism.L2.Host.CharFrame D) : Prop :=
  ∀ [Algebra J.Q.c.F D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (R : RealDat D A J.Q.c.F) (μ0 : T0), R.C = C → R.toLevCh.Is μ0 → CoreTies L EX J R ∧
      ∀ (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T0) (S : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))),
        CoreTies L EX J { R with mu := mu, twPl := S }

theorem exists_core_coreTies (D : D7) (L : SizeData₂ D) (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D)
    (h₁ : FieldOK0 D D.host.pde) (h₂ : FieldOK0 D D.host.pde') (hs : FieldSmall D L)
    (hE : ∀ k, barE D (EX.piG k) ∈ (C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)))
    (hd : ∀ x, ((C.del.1 x : ℂˣ) : ℂ) ∈ FO D) (hd' : ∀ x, ((C.del'.1 x : ℂˣ) : ℂ) ∈ FO D)
    (chi₀ : ℕ → (Formalism.L2.Theta.AE D)ˣ →* Circle) (hchi : ChiOK D chi₀) :
    ∃ J : CoreJ D, LawsJ J ∧ LawsCore J.toCore ∧ J.Q.Canon ∧ (∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) ∧ HalfEX J.toCore EX ∧
      J.pb = C.P.pb ∧ (∀ j, J.chiW j J.σ₀ = chi₀ j) ∧ (∃ a : Algebra J.Q.c.F D.what₂.LL, @AlgTie D J a) ∧ IsParametersCompatibleWithCharFrame L EX J C := by
  obtain ⟨J, hJ, hc, hcan, hpb, hr, hχ⟩ := exists_coreJ_of_chiOK_noVol D h₁.full h₁.zetaM C.P.pb C.P.pb_over chi₀ hchi
  have hH : HalfEX J.toCore EX := fun i => by
    show barE D (EX.piG i) ∈ (J.pb i).asIdeal.map _
    rw [hpb]
    exact hE i
  refine ⟨J, hJ, hc, hcan, hr, hH, hpb, hχ, ⟨_, algTie_algTop J hJ.pins.2.2.1⟩, ?_⟩
  rintro _ G _ _ Pl0 T0 A R μ0 rfl hL
  exact ⟨coreTies_of_is hL hpb hc hcan hr hH h₁ h₂ hs hd hd', fun mu S =>
    coreTies_of_is (R := { R with mu := mu, twPl := S }) hL hpb hc hcan hr hH h₁ h₂ hs hd hd'⟩

theorem exists_frame_of_richRec (D : D7) (EX : ErrX D) (h : RichRec D) (h₁ : FieldOK0 D D.host.pde)
    (h₂ : FieldOK0 D D.host.pde') : ∃ C : Formalism.L2.Host.CharFrame D,
      (∀ k, barE D (EX.piG k) ∈ (C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧
      (∀ x, ((C.del.1 x : ℂˣ) : ℂ) ∈ FO D) ∧ (∀ x, ((C.del'.1 x : ℂˣ) : ℂ) ∈ FO D) ∧
      ∃ Lc : LevCh D (Option Bool), Lc.C = C ∧ Lc.Is none ∧ Lc.xiH (some false) = C.del ∧ Lc.xiH (some true) = C.del' ∧
        (∃ PP ∈ Lc.Q (some false), ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
        ∃ PP ∈ Lc.Q (some true), ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  choose pb g1 g2 using exists_prime_bar_piG D EX
  obtain ⟨C, hC⟩ := exists_charFrame D ⟨pb, g1⟩ h.1 h.2.1 h.2.2.1
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K D.host.pde_prime
  obtain ⟨P₂, hP₂⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K D.host.pde'_prime
  obtain ⟨Lc, a1, a2, a3, a4, a5, a6⟩ := exists_levCh_twisted C h.1 h.2.1 h₁.split h₂.split P₁ P₂ hP₁ hP₂
  obtain ⟨w₁, hw₁⟩ := aboveK_nonempty P₁
  obtain ⟨w₂, hw₂⟩ := aboveK_nonempty P₂
  exact ⟨C, by rw [hC]; exact g2, isDelta_mem C.isDel h.2.2.2, isDelta_mem C.isDel' h.2.2.2, Lc, a1, a2, a3, a4,
    ⟨w₁, a5 ▸ hw₁, overP_of_under hP₁ (mem_aboveK.1 hw₁)⟩, w₂, a6 ▸ hw₂, overP_of_under hP₂ (mem_aboveK.1 hw₂)⟩

theorem exists_coreTies_of_zeroFreeRegion : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount →
    Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → GlobalTheory.NT.RayField →
    ∀ x : ℝ, ∃ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D)
      (J : CoreJ D), RecOK D x ∧ DV.KapDef D ∧ PageNum Tp x ∧ FieldSmall D L ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (15 * classNumber D.host.E) ∈ FO D ∧
      (∀ y, ((C.del.1 y : ℂˣ) : ℂ) ∈ FO D) ∧ (∀ y, ((C.del'.1 y : ℂˣ) : ℂ) ∈ FO D) ∧
      (∃ Lc : LevCh D (Option Bool), Lc.C = C ∧ Lc.Is none ∧ Lc.xiH (some false) = C.del ∧ Lc.xiH (some true) = C.del' ∧
        (∃ PP ∈ Lc.Q (some false), ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
        ∃ PP ∈ Lc.Q (some true), ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
      LawsJ J ∧ LawsCore J.toCore ∧ J.Q.Canon ∧ HalfEX J.toCore EX ∧ J.pb = C.P.pb ∧
      (∃ a : Algebra J.Q.c.F D.what₂.LL, @AlgTie D J a) ∧ IsParametersCompatibleWithCharFrame L EX J C := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 x
  obtain ⟨D, hD, hR⟩ := exists_richRec_of_zeroFreeRegion p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 x
  obtain ⟨EX⟩ := hD.err
  obtain ⟨L, Pm, Tp, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hD.num
  obtain ⟨C, c1, c2, c3, c4⟩ := exists_frame_of_richRec D EX hR hD.one hD.two
  obtain ⟨J, j1, j2, j3, -, j5, j6, -, j8, j9⟩ := exists_core_coreTies D L EX C hD.one hD.two n8 c1 c2 c3 _ (chiOK_one D)
  exact ⟨D, L, Pm, Tp, EX, C, J, hD, n1, ⟨n2, n3, n4, n5, n6, n7⟩, n8, hR.2.2.2, c2, c3, c4, j1, j2, j3, j5, j6, j8, j9⟩

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslates
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.TranslatesDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermMat {G γ : Matrix (Fin r) (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec γ v) (Matrix.mulVec γ w) = herm G v w) :
    γᵀ * G * γ.map cc = G := by
  ext c d
  have h1 := h (Pi.single c 1) (Pi.single d 1)
  simp only [herm, Matrix.mulVec_single_one] at h1
  have h2 : (∑ a, ∑ b, (Pi.single c (1 : E) : Fin r → E) a * G a b *
      cc ((Pi.single d (1 : E) : Fin r → E) b)) = G c d := by simp [Pi.single_apply, cc]
  rw [← h2, ← h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem gramLact {G : Matrix (Fin r) (Fin r) E} {γ : GL (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) w) = herm G v w)
    (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G ((γ : Matrix (Fin r) (Fin r) E).map τ * M) = gram τ G M := by
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ := by
    ext a b; simp [cc, NumberField.IsCMField.complexEmbedding_complexConj]
  have key : ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
      ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) = G.map τ := by
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hermMat h]
  rw [FrameDegreeData.gram_eq, FrameDegreeData.gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  calc Mᵀ * ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
        (((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) * M.map (starRingEnd ℂ))
      = Mᵀ * (((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
        ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem lactGG {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {p0 : ℕ} {γ : GL (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) w) = herm G v w)
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : lact γ x ∈ GG Ψ G p0 := by
  intro τ
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    refine mul_ne_zero ?_ (hx τ).1
    have hd : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det := by
      rw [RingHom.map_det]; rfl
    rw [hd]
    exact (map_ne_zero τ.1).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)
  · have e : dmin G (lact γ x) τ i = dmin G x τ i := by
      unfold dmin; rw [hm, gramLact h]
    rw [e]; exact (hx τ).2 i

theorem lactMul {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem castGG {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {G : Matrix (Fin r) (Fin r) E} {p0 : ℕ}
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : castFrame h x ∈ GG Ψ' G p0 := by
  subst h; exact hx

section Two

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem domOfComp (c : C) {x : Frame (M.comp c).Ψ r} (hx : x ∈ (M.comp c).dom) :
    castFrame (M.comp_Ψ c) x ∈ M.dom := by
  have h := castGG (M.comp_Ψ c) hx
  rw [M.comp_Gm c, M.comp_basePoint c] at h
  exact h

theorem domToComp (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    castFrame (M.comp_Ψ c).symm x ∈ (M.comp c).dom := by
  have hx' : x ∈ GG M.Ψ (M.comp c).Gm (M.comp c).p0 := by
    rw [M.comp_Gm c, M.comp_basePoint c]; exact hx
  exact castGG (M.comp_Ψ c).symm hx'

theorem trDom (u : U) (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) : lact (M.tr u c) x ∈ M.dom :=
  lactGG (M.tr_herm u c) hx

theorem ssLact {la : Wt M.Ψ r} {F : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (c : C)
    {γ : GL (Fin r) E} (hγ : γ ∈ (M.comp c).Γ) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    F c (lact γ x) = F c x := by
  have h1 := (hF c).1.1.2.2 γ hγ (castFrame (M.comp_Ψ c).symm x) (domToComp M c hx)
  rw [M.χ_one c _ γ hγ, one_mul] at h1
  exact h1

theorem ssZero (la : Wt M.Ψ r) : (0 : C → Frame M.Ψ r → ℂ) ∈ M.SS la := by
  intro c
  exact ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ ξ x 0⟩

theorem ssAdd {la : Wt M.Ψ r} {F G : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (hG : G ∈ M.SS la) :
    F + G ∈ M.SS la := by
  intro c
  have h := hF c
  have h' := hG c
  have e : (fun y => (F + G) c (castFrame (M.comp_Ψ c) y)) =
      (fun y => F c (castFrame (M.comp_Ψ c) y)) + (fun y => G c (castFrame (M.comp_Ψ c) y)) := rfl
  rw [e]
  exact ⟨BoundedSectionAlgebra.bdd_add _ h.1 h'.1, fun ξ hξ x hx => by
    rw [BoundedSectionAlgebra.fj_add _ h.1 h'.1 hξ hx, h.2 ξ hξ x hx, h'.2 ξ hξ x hx, add_zero]⟩

theorem ssSum {la : Wt M.Ψ r} {ι : Type} (s : Finset ι) (f : ι → C → Frame M.Ψ r → ℂ)
    (h : ∀ i ∈ s, f i ∈ M.SS la) : ∑ i ∈ s, f i ∈ M.SS la :=
  Finset.sum_induction f (fun F => F ∈ M.SS la) (fun _ _ ha hb => ssAdd M ha hb) (ssZero M la) h

end Two

end GlobalTheory.TranslatesDet

namespace GlobalTheory.TranslatesDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem detNeAt [Fintype U] [DecidableEq U] {la : Wt M.Ψ r} {u u0 : C → Frame M.Ψ r → ℂ}
    (hu : u ∈ M.SS la) {c0 : C} {x0 : Frame M.Ψ r} (hx0 : x0 ∈ M.dom) (hne : u c0 x0 ≠ 0)
    (hz : ∀ h : U, h ≠ 1 → M.pull h u c0 x0 = 0)
    (hrep : ∀ (g : U) (y : Frame M.Ψ r), u0 (g • c0) y = u (g • c0) y) (k : U) :
    ∃ x ∈ M.dom, M.detTr u0 (k • c0) x ≠ 0 := by
  refine ⟨lact (M.tr k c0) x0, trDom M k c0 hx0, ?_⟩
  have ht1 : M.tr 1 c0 ∈ (M.comp c0).Γ := by
    have h := M.tr_mul 1 1 c0
    simp only [mul_one, one_smul] at h
    have e : M.tr 1 c0 * (M.tr 1 c0 * M.tr 1 c0)⁻¹ = (M.tr 1 c0)⁻¹ := by group
    rw [e] at h
    exact inv_mem_iff.mp h
  have ha : M.pull 1 u c0 x0 ≠ 0 := by
    simp only [TwoLevels.pull, one_smul]
    rw [ssLact M hu c0 ht1 hx0]
    exact hne
  have entry : ∀ g : U, M.pull g u0 (k • c0) (lact (M.tr k c0) x0) = M.pull (g * k) u c0 x0 := by
    intro g
    have hzd : lact (M.tr g (k • c0)) (lact (M.tr k c0) x0) ∈ M.dom :=
      trDom M g (k • c0) (trDom M k c0 hx0)
    have e1 : lact (M.tr (g * k) c0) x0 =
        lact (M.tr (g * k) c0 * (M.tr g (k • c0) * M.tr k c0)⁻¹)
          (lact (M.tr g (k • c0)) (lact (M.tr k c0) x0)) := by
      rw [lactMul (M.tr g (k • c0)) (M.tr k c0) x0, lactMul, inv_mul_cancel_right]
    simp only [TwoLevels.pull]
    rw [e1, ← mul_smul, hrep (g * k)]
    exact (ssLact M hu ((g * k) • c0) (M.tr_mul g k c0) hzd).symm
  let σ : Equiv.Perm U := (Equiv.inv U).trans (Equiv.mulRight k⁻¹)
  have key : ∀ h h' : U, h * h' * k = 1 ↔ σ h = h' := by
    intro h h'
    show h * h' * k = 1 ↔ h⁻¹ * k⁻¹ = h'
    constructor
    · intro e
      have e2 : h⁻¹ * (h * h' * k) * k⁻¹ = h' := by group
      rw [e] at e2
      simpa using e2
    · intro e
      rw [← e]
      group
  have hmat : (Matrix.of fun h h' : U => M.pull (h * h') u0 (k • c0) (lact (M.tr k c0) x0)) =
      (M.pull 1 u c0 x0 • (1 : Matrix U U ℂ)).submatrix σ id := by
    ext h h'
    rw [Matrix.of_apply, entry, Matrix.submatrix_apply, id, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases e : h * h' * k = 1
    · rw [if_pos ((key h h').1 e), e, mul_one]
    · rw [if_neg (fun e' => e ((key h h').2 e')), mul_zero]
      exact hz _ e
  unfold TwoLevels.detTr
  rw [hmat, Matrix.det_permute, Matrix.det_smul, Matrix.det_one, mul_one]
  refine mul_ne_zero ?_ (pow_ne_zero _ ha)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem independentTranslates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    IndependentTranslates E := by
  intro E _ _ _ r U C _ _ _ _ _ M hL s hs hsle
  classical
  have hB : ∀ c : C, ∃ x ∈ (M.comp c).dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) x := fun c => by
    obtain ⟨x, hx, h1, -⟩ := GlobalTheory.T.existsBalancedFrameCMUnitary_proof E r (M.comp c)
    exact ⟨x, hx, h1⟩
  choose xb hxb hnc using hB
  have hI : ∀ c : C, ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c (castFrame (M.comp_Ψ c) (xb c)) ≠ 0 ∧
      (∀ h : U, h ≠ 1 → M.pull h u c (castFrame (M.comp_Ψ c) (xb c)) = 0) ∧
      ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := fun c =>
    GlobalTheory.T.exists_cuspForm_nonzero_at_one_lift E r U C M hL s hs hsle c _ (hnc c) (domOfComp M c (hxb c))
  choose uc huS hu0 hu1 hu2 using hI
  haveI : Fintype (Quotient (MulAction.orbitRel U C)) := Fintype.ofFinite _
  have hsum : ∀ c' y, (∑ q : Quotient (MulAction.orbitRel U C), uc q.out) c' y =
      uc (Quotient.mk (MulAction.orbitRel U C) c').out c' y := by
    intro c' y
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_eq_single (Quotient.mk (MulAction.orbitRel U C) c') (fun q _ hq => ?_)
      (fun h => absurd (Finset.mem_univ _) h)
    refine hu2 q.out c' (fun h hh => hq ?_) y
    have e : (Quotient.mk (MulAction.orbitRel U C) q.out) = Quotient.mk (MulAction.orbitRel U C) c' :=
      Quotient.sound (MulAction.orbitRel_apply.2 ⟨h⁻¹, by show h⁻¹ • c' = q.out; rw [← hh, inv_smul_smul]⟩)
    rwa [Quotient.out_eq] at e
  have hrep : ∀ (q : Quotient (MulAction.orbitRel U C)) (g : U) (y : Frame M.Ψ r),
      (∑ q' : Quotient (MulAction.orbitRel U C), uc q'.out) (g • q.out) y = uc q.out (g • q.out) y := by
    intro q g y
    rw [hsum]
    have e : Quotient.mk (MulAction.orbitRel U C) (g • q.out) = q :=
      (Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, rfl⟩)).trans (Quotient.out_eq q)
    rw [e]
  refine ⟨∑ q : Quotient (MulAction.orbitRel U C), uc q.out,
    ssSum M _ _ (fun q _ => huS q.out), fun c => ?_⟩
  obtain ⟨m, hm⟩ : (Quotient.mk (MulAction.orbitRel U C) c).out ∈ MulAction.orbit U c :=
    MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel U C) c)))
  have hk : m⁻¹ • (Quotient.mk (MulAction.orbitRel U C) c).out = c := by
    rw [← hm, inv_smul_smul]
  rw [← hk]
  exact detNeAt M (huS _) (domOfComp M _ (hxb _)) (hu0 _) (hu1 _) (hrep _) m⁻¹

end GlobalTheory.TranslatesDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspNe
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ScalarPoin
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem qS_base (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (k : ℕ) : qS X x0 k x0 = 1 := by
  unfold qS
  refine Finset.prod_eq_one fun τ _ => ?_
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [KU.Mx, Matrix.nonsing_inv_mul _ hu, KU.tl_one]
  have h1 : (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ).toBlocks₂₂ = 1 := by
    ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  rw [h1]
  simp

end GlobalTheory.ScalarPoin

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory GlobalTheory.ScalarPoin in
theorem GlobalTheory.ScalarPoin.exists_cusp_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ y ∈ X.dom, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), P y ≠ 0 := by
  intro E _ _ _ r X hp0 hpr hχ y hy N
  obtain ⟨x0, ho, b, hb, rfl⟩ := ortho_holds r X y hy
  have hPD := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  have hx0 : x0 ∈ X.dom := KU.orth_dom X ho
  set bb : ℝ := 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 with hbbdef
  have hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb := by linarith
  obtain ⟨s0, hs0⟩ := GlobalTheory.T.lintegral_potentialWeight_chart_lt_top E r X x0 ho
  obtain ⟨k0, hk0⟩ := exists_nat_ge ((s0 + bb) / 2)
  have hla : ∀ k : ℕ, (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then (((2 * k) / 2 : ℕ) : ℤ)
      else -(((2 * k) / 2 : ℕ) : ℤ)) = laS X k := by
    intro k; funext τ j; simp [laS]
  have hχk : ∀ k : ℕ, ∀ γ ∈ X.Γ, X.χ (laS X k) γ = 1 := by
    intro k γ hγ
    have := hχ (2 * k) (even_two_mul k) γ hγ
    rwa [hla k] at this
  have hIn : ∀ k : ℕ, k0 ≤ k →
      InAt X x0 (fun x => ENNReal.ofReal (Real.exp (-phla X (laS X k) x))) bb (fun _ => (1 : ℂ)) := by
    intro k hk
    have hs : s0 ≤ 2 * (k : ℝ) - bb := by
      have : ((s0 + bb) / 2 : ℝ) ≤ k := le_trans hk0 (by exact_mod_cast hk)
      linarith
    unfold InAt
    refine lt_of_le_of_lt (le_of_eq ?_) (hs0 _ hs)
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0)] with z hz
    rw [GlobalTheory.T.metric_scalarPoincareWeight_eq_two_mul_potential E r X x0 ho k z hz]
    simp only [norm_one, one_pow, kaF]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_div, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  have hpo := fun k (hk : k0 ≤ k) => poin_holds r X x0 ho hPD (laS X k) _ bb (DivUpPf.metricW_exp X _)
    (DivUpPf.wLower_exp X _) hbb (fun _ => (1 : ℂ)) (qS X x0 k) (differentiableOn_const _) (hIn k hk)
    ⟨GlobalTheory.T.scalarPoincareDetRatioPower_differentiableOn E r X x0 ho k, fun x _ b hb => GlobalTheory.T.scalarPoincareDetRatioPower_rmul_borel E r X x0 k x b hb⟩ (fun z _ => qS_cpt X ho k z)
  set a : X.Γ → ℂ := fun γ => qS X x0 1 (lact γ.1 x0) with ha
  have ha1 : a 1 = 1 := by
    simp only [ha, OneMemClass.coe_one, KU.lact_one]
    exact qS_base X ho 1
  have hterm : ∀ k (γ : X.Γ), (X.χ (laS X k) γ.1)⁻¹ * qS X x0 k (lact γ.1 x0) = a γ ^ k := by
    intro k γ
    rw [hχk k γ.1 γ.2, inv_one, one_mul, qS_pow]
  have hsum : Summable fun γ : X.Γ => ‖a γ‖ ^ k0 := by
    have h := (hpo k0 le_rfl).1 x0 hx0
    simp_rw [hterm k0, norm_pow] at h
    exact h
  have hle : ∀ γ : X.Γ, ‖a γ‖ ≤ 1 := fun γ => (GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one E r X x0 ho γ.1 γ.2).1
  have hlt : ∀ γ : X.Γ, γ ≠ 1 → ‖a γ‖ < 1 := by
    intro γ hne
    refine lt_of_le_of_ne (hle γ) fun heq => hne (Subtype.ext ?_)
    exact GlobalTheory.T.eq_one_of_orthonormal_conj_block_upper_triangular E r X x0 ho γ.1 γ.2 ((GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one E r X x0 ho γ.1 γ.2).2 heq)
  obtain ⟨k, hk, hne⟩ := GlobalTheory.T.exists_ge_tsum_pow_ne_zero_of_single_unit a 1 k0 ha1 hle hlt hsum (max N (k0 + 1))
  have hk0k : k0 ≤ k := le_trans (by omega) hk
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  obtain ⟨τ0⟩ : Nonempty X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hτ : τ ∈ X.Ψ
    · exact ⟨⟨τ, hτ⟩⟩
    · exact ⟨⟨_, not_not.mp ((X.cmType τ).not.mp hτ)⟩⟩
  have hB := (hpo k hk0k).2.1
  refine ⟨2 * k, le_trans (le_max_left _ _) (le_trans hk (by omega)), by omega, even_two_mul k, ?_⟩
  rw [hla k]
  refine ⟨poin X (laS X k) (qS X x0 k), ?_, ?_⟩
  · refine cuspStatement_holds r X (laS X k) τ0 hp0 hpr (fun i j hij hjp => ?_) (fun i0 i1 h0 h1 => ?_) _ hB
    · simp only [laS]
      split_ifs with h1 h2 <;> omega
    · simp only [laS]
      rw [if_neg (by omega), if_pos (by omega)]
      omega
  · rw [hB.1.2.1 x0 hx0 b hb]
    refine mul_ne_zero ?_ ?_
    · unfold bchar
      exact Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
        zpow_ne_zero _ (FrameDegreeData.bdiag_ne X hb τ i)
    · unfold poin
      simp_rw [hterm k]
      exact hne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegralStatement
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearEquiv_mul_twistingSection_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∃ φ : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀), (∀ f, (φ f : Rul Xo c) = f * s.sig) ∧ (∀ g, (φ.symm g : Rul Xo c) = g * s.inv) ∧ (∀ a : c.F, a ≠ 0 → (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) → ∀ f ∈ latOn U Z G, ∀ g : cuspOn U Z (G + G₀), (g : Rul Xo c) = a • (φ f : Rul Xo c) → g ∈ latOn U Z (G + G₀)) ∧ (∀ b : c.F, b ≠ 0 → (∀ w, s.hi w ≤ (vAdd w b : ℝ)) → ∀ g ∈ latOn U Z (G + G₀), ∀ f : cuspOn U Z G, (f : Rul Xo c) = b • (φ.symm g : Rul Xo c) → f ∈ latOn U Z G) := by
  first | exact @GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral | exact GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral | (intros; apply GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReadingStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_quotient_of_continuous_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (e e' : Ix Dw → ℤ) (f g : Rul Xo c), f ∈ secZ Xo c e → f ∈ suppOn Z → g ∈ secZ Xo c e' → g ∈ suppOn Z → f ≠ 0 → ∀ σ, GoodEmb c σ → ∀ q : FDSec (U σ).X, (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) g z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∃ s ∈ secZ Xo c (e' - e), idem Z * s = s ∧ s * f = g := by
  first | exact @GlobalTheory.SecDivision.exists_quotient | exact GlobalTheory.SecDivision.exists_quotient | (intros; apply GlobalTheory.SecDivision.exists_quotient <;> assumption)
end

