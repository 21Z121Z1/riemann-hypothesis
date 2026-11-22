import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0703
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0478
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0467
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0540
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0559
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntegrableAndBoundedLinearForm

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBaseUniq
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem smul_eq_of_adj {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {c : R} {A A' X X' G H : Matrix n n R}
    (h : A * (G * X) = G) (h' : A' * (G * X') = G) (hH : G * H = 1) (e : c • A = c • A') : c • X = c • X' := by
  have h1 : A * G * (X * H) = 1 := by rw [← Matrix.mul_assoc, Matrix.mul_assoc A, h, hH]
  have h2 : X * H * (A * G) = 1 := mul_eq_one_comm.1 h1
  have h3 : A * G * (c • X) = A * G * (c • X') := by
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, h, ← Matrix.smul_mul, e, Matrix.smul_mul, h']
  have h4 := congrArg (X * H * ·) h3
  simp only [← Matrix.mul_assoc (X * H) (A * G), h2, Matrix.one_mul] at h4
  exact h4

theorem eq_of_halves {R : Type} [CommRing R] {n : Type} [DecidableEq n] {a b : R} {X X' : Matrix n n R}
    (h : ∀ i j, (a + b) * (X - 1) i j = (X - 1) i j) (h' : ∀ i j, (a + b) * (X' - 1) i j = (X' - 1) i j)
    (ha : a • X = a • X') (hb : b • X = b • X') : X = X' := by
  ext i j
  have k1 : a * X i j = a * X' i j := congrFun (congrFun ha i) j
  have k2 : b * X i j = b * X' i j := congrFun (congrFun hb i) j
  have k3 := h i j
  have k4 := h' i j
  simp only [Matrix.sub_apply] at k3 k4
  linear_combination k1 + k2 - k3 + k4

theorem supp_shrink {R : Type} [CommRing R] {n : Type} [DecidableEq n] {a b a' b' : R} {X : Matrix n n R}
    (h : ∀ i j, (a + b) * (X - 1) i j = (X - 1) i j) (ha : (a - a') • X = (a - a') • (1 : Matrix n n R))
    (hb : (b - b') • X = (b - b') • (1 : Matrix n n R)) (i j : n) : (a' + b') * (X - 1) i j = (X - 1) i j := by
  have k1 : (a - a') * X i j = (a - a') * (1 : Matrix n n R) i j := congrFun (congrFun ha i) j
  have k2 : (b - b') * X i j = (b - b') * (1 : Matrix n n R) i j := congrFun (congrFun hb i) j
  have k3 := h i j
  simp only [Matrix.sub_apply] at k3 ⊢
  linear_combination k3 - k1 - k2

variable {D : D7}

theorem smul_conj {V : HSp D} {e : AE D} {g g' : GA D V} (h : e • mt V g = e • mt V g') :
    cA D e • mt V g = cA D e • mt V g' :=
  smul_eq_of_adj (mt_unitary V g) (mt_unitary V g') (gA_mul_giA V)
    ((adj_smul e _).symm.trans ((congrArg adj h).trans (adj_smul e _)))

theorem smul_eq_of_loc {V : HSp D} {e : AE D} (h0 : infPart D e = 0) {g g' : GA D V}
    (h : ∀ w : Pl D.host.E, piAt w e = 0 ∨ GlobalTheory.StdFrames.loc w (Lev.finE V g) = GlobalTheory.StdFrames.loc w (Lev.finE V g')) :
    e • mt V g = e • mt V g' := by
  refine mx_ext ?_ fun w => ?_
  · rw [map_smul_mx, map_smul_mx, h0, zero_smul, zero_smul]
  · rw [map_smul_mx, map_smul_mx]
    rcases h w with h | h
    · rw [h, zero_smul, zero_smul]
    · exact congrArg (piAt w e • ·) (congrArg Units.val h)

theorem loc_eq_of_inBasis {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) {x y : GL (Fin n) (Lev.EAf D)}
    (e : inBasis h β w x = inBasis h β w y) : GlobalTheory.StdFrames.loc w x = GlobalTheory.StdFrames.loc w y := by
  have e1 : GlobalTheory.StdFrames.loc w (β⁻¹ * x * β⁻¹⁻¹) = GlobalTheory.StdFrames.loc w (β⁻¹ * y * β⁻¹⁻¹) :=
    (GlobalTheory.StepData.reGL _).injective e
  rw [map_mul, map_mul, map_mul, map_mul] at e1
  exact mul_left_cancel (mul_right_cancel e1)

theorem isFinOf_unique {V : HSp D} {g b b' : GA D V} (h : IsFinOf g b) (h' : IsFinOf g b') : b = b' := by
  obtain ⟨hb, a, ha, e⟩ := h
  obtain ⟨hb', a', ha', e'⟩ := h'
  have i : infHom V b = infHom V b' := (MonoidHom.mem_ker.1 hb).trans (MonoidHom.mem_ker.1 hb').symm
  have f : finHom V b = finHom V b' := by
    have := congrArg (finHom V) (e.trans e'.symm)
    rwa [map_mul, map_mul, MonoidHom.mem_ker.1 ha, MonoidHom.mem_ker.1 ha', one_mul, one_mul] at this
  have f' : Lev.finE V b = Lev.finE V b' := congrArg (Formalism.UG.bc (Lev.swapAE D)) f
  refine Subtype.ext (Units.ext (mx_ext (congrArg Units.val i) fun w => ?_))
  exact congrArg (fun z => (GlobalTheory.StdFrames.loc w z).val) f'

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem exists_indicator (P : Finset (Pl D.host.E)) :
    ∃ e : AE D, infPart D e = 0 ∧ (∀ w ∈ P, piAt w e = 1) ∧ ∀ w ∉ P, piAt w e = 0 := by
  obtain ⟨X, a, b, c⟩ := exists_lift (n := 1) P fun _ => 1
  exact ⟨X 0 0, congrFun (congrFun a 0) 0, fun w hw => (congrFun (congrFun (b ⟨w, hw⟩) 0) 0).trans (one_apply_eq _),
    fun w hw => congrFun (congrFun (c w hw) 0) 0⟩

theorem stair_off (t : T) {w : Pl D.host.E} (hw : w ∉ G.pl.W0) (j : ℕ) :
    stair (locGrid G t w) (unifAt w) (cosExp G w) j = 1 := by
  rw [(depthAt_of_notMem G hw).1, stair]
  simp only [zero_mul, pow_zero]
  exact Units.ext diagonal_one

theorem supp_base (B : Frames G) {t : T} {r : GA D (G.V (.grid D.R.m 0))}
    (h : HasLoc t B (Nat.zero_le _) r fun w => (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹) {e₀ : AE D}
    (h0 : infPart D e₀ = 0) (h1 : ∀ w ∈ G.pl.W0, piAt w e₀ = 1) (h2 : ∀ w ∉ G.pl.W0, piAt w e₀ = 0) : SuppAt e₀ _ r := by
  classical
  obtain ⟨e, he, hs, hl⟩ := h
  obtain ⟨e0, e1, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  replace e1 : ∀ w ∈ locPl G t, piAt w e = 1 := e1
  replace e2 : ∀ w ∉ locPl G t, piAt w e = 0 := e2
  have hsub : ∀ w ∈ G.pl.W0, w ∈ locPl G t := fun w hw => by
    unfold locPl; convert Finset.mem_union_left _ hw
  have k : (e - e₀) • mt _ r = (e - e₀) • mt _ (1 : GA D (G.V (.grid D.R.m 0))) := by
    refine smul_eq_of_loc (by rw [RingHom.map_sub, e0, h0, sub_self]) fun w => ?_
    by_cases hw : w ∈ G.pl.W0
    · exact .inl (by rw [RingHom.map_sub, e1 w (hsub w hw), h1 w hw, sub_self])
    · by_cases hp : w ∈ locPl G t
      · refine .inr (loc_eq_of_inBasis _ (B.β D.R.m 0) w ((hl ⟨w, hp⟩).trans ?_))
        rw [map_one, map_one]
        exact inv_eq_one.2 (stair_off t hw 0)
      · exact .inl (by rw [RingHom.map_sub, e2 w hp, h2 w hw, sub_self])
  have k' := smul_conj k
  rw [RingHom.map_sub] at k'
  rw [GlobalTheory.MixModel.mt_one] at k k'
  exact supp_shrink hs k k'

theorem base_zero (B : Frames G) {t t' : T} {r r' : GA D (G.V (.grid D.R.m 0))}
    (h : HasLoc t B (Nat.zero_le _) r fun w => (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹)
    (h' : HasLoc t' B (Nat.zero_le _) r' fun w => (stair (locGrid G t' w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹) : r = r' := by
  classical
  obtain ⟨e₀, h0, h1, h2⟩ := exists_indicator (D := D) G.pl.W0
  have s := supp_base B h h0 h1 h2
  have s' := supp_base B h' h0 h1 h2
  obtain ⟨-, -, -, hl⟩ := h
  obtain ⟨-, -, -, hl'⟩ := h'
  have hsub : ∀ t, ∀ w ∈ G.pl.W0, w ∈ locPl G t := fun t w hw => by
    unfold locPl; convert Finset.mem_union_left _ hw
  have k : e₀ • mt _ r = e₀ • mt _ r' := by
    refine smul_eq_of_loc h0 fun w => ?_
    by_cases hw : w ∈ G.pl.W0
    · exact .inr (loc_eq_of_inBasis _ (B.β D.R.m 0) w ((hl ⟨w, hsub t w hw⟩).trans (hl' ⟨w, hsub t' w hw⟩).symm))
    · exact .inl (h2 w hw)
  exact Subtype.ext (Units.ext (eq_of_halves s s' k (smul_conj k)))

theorem isBase_eq (B : Frames G) {t t' : T} {b b' : Pts G} (h : IsBase t B b) (h' : IsBase t' B b') : b = b' := by
  funext j
  by_cases h0 : j = 0
  · subst h0
    exact base_zero B h.1 h'.1
  · by_cases hj : j ∈ GlobalTheory.RowVal.idx D
    · obtain ⟨δ, hδ, hb⟩ := h.2.1 j hj
      obtain ⟨δ', hδ', hb'⟩ := h'.2.1 j hj
      obtain rfl := isTilt_unique (by have := idx_le hj; omega) hδ hδ'
      exact isFinOf_unique hb hb'
    · rw [h.2.2 j h0 hj, h'.2.2 j h0 hj]

theorem isBase_unique : Big fun ch => ∀ t t' b b', IsBase t ch.S.B b → IsBase t' ch.S.B b' → b = b' :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ _ _ _ _ h h' => isBase_eq ch.S.B h h'⟩⟩

end GlobalTheory.RowBaseUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelFiniteExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict.LineStab
theorem ptF_one' {D : D7} {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (f : WO V W → ℂ) : ptF ψ θ A B f 1 = f := by
  have h1 : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp [MvPolynomial.coe_basisMonomials]
  rw [h1]
  simp only [ptF, pureTensorO, pureTensorL]
  rw [Module.Basis.constr_basis]
  simp [opPow]

theorem thO_zero' {m k d : ℕ} {D : D7} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) :
    GlobalTheory.TripleRead.thO Mo ψ G e 0 = 0 := by
  funext x
  simp only [GlobalTheory.TripleRead.thO, GlobalTheory.WeilM.thetaSum, Pi.zero_apply]
  refine (tsum_congr fun ξ => ?_).trans tsum_zero
  exact mul_zero _

theorem conjU_one' {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem det_sgn_gram {D : D7} (ε : Bool) (M : HSp D) (h : (GlobalTheory.RealDict.sgE (D := D) ε • M.gram).det ≠ 0) :
    ((sgn ε M).gram).det ≠ 0 := by
  have hg : (sgn ε M).gram = -(GlobalTheory.RealDict.sgE (D := D) ε • M.gram) := by
    cases ε <;> ext i j <;> simp [GlobalTheory.RealDict.sgE, sgn, HSpace.gram]
  rw [hg, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

theorem derivLine_mem_map : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
          f₁ ∈ N.map Φ := by
  intro hPr D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hH hR Φ hΦi hΦr hF N hN γ hγ f hf f₁ hA
  obtain ⟨P, hPN, rfl⟩ := Submodule.mem_map.mp hf
  obtain ⟨f₀, r, hvac, hf₀, hΦ⟩ := hF
  obtain ⟨h, Y, hY, hγh, hD⟩ := GlobalTheory.T.skewSpaceLine_oneParam_fockDerivative D ψ θ ε M X A B χS χT ω eS eT hθ hW hE Ws hR.JW γ hγ
  have hP'N : (∑ t, GlobalTheory.RealQuot.actT ε A B eS t (Y t) P) ∈ N :=
    Submodule.sum_mem _ (fun t _ => hN ⟨(t, Y t), hY t⟩ P hPN)
  have hr : ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) r x ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) r = 0 := funext hc
    have h1 := (hΦ 1).2
    rw [h0, thO_zero', ptF_one'] at h1
    exact hf₀ h1.symm
  have hRest : ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) g r :=
    GlobalTheory.Twist.RestrictionTransfer.rest_transfer D.host.F (Φ 1) r (hΦ 1).1 hr
  have hψ' := hR.psi
  subst hψ'
  have key : ∀ x, GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x =
      ptF (V := sgn ε M) ψ' θ (frSgn ε A) B f₀ (∑ t, GlobalTheory.RealQuot.actT ε A B eS t (Y t) P) x := by
    intro x
    have d1 := GlobalTheory.T.real_dictionary_hypotheses hPr D Xs Ws Mo ψ' χX χW om τ hH hR.good γ hγ (Φ P) f₁ r (hRest _) (hRest _) hA
      (sgn ε M).gram (Equiv.refl (Fin X.rank)) x
    have d2 := hD f₀ hvac P x
    have hfun : (fun t : ℝ => GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
        (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r)) x) =
        fun t => ω (1, h t) (ptF (V := sgn ε M) ψ' θ (frSgn ε A) B f₀ P) x := by
      funext t
      have e1 := hR.transp _ (hRest (Φ P)).2 1 (h t)
      rw [conjU_one'] at e1
      rw [hγh t, e1, (hΦ P).2]
    rw [hfun] at d1
    exact d1.unique d2
  have hthO : GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) =
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ (∑ t, GlobalTheory.RealQuot.actT ε A B eS t (Y t) P)) r) := by
    funext x
    rw [key x, (hΦ _).2]
  have hdet : ((sgn ε M).gram).det ≠ 0 := det_sgn_gram ε M (by rw [← hR.JX]; exact hH.2.2.2.1)
  have ht := GlobalTheory.ThetaTransformInj.thO_injective D Xs Ws Mo ψ' χX χW om τ hH hR.good (sgn ε M).gram
    (Equiv.refl (Fin X.rank)) hdet _ (hRest f₁).2 _ (hRest _).2 hthO
  have hr' : ∃ x, r x ≠ 0 := by
    obtain ⟨x, hx⟩ := hr
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens at hx
    exact ⟨x, right_ne_zero_of_mul hx⟩
  exact Submodule.mem_map.mpr ⟨_, hP'N, (GlobalTheory.ArchCancel.eq_of_tens_eq D.host.F r (hRest f₁).1 hr' f₁ _ ht).symm⟩
end GlobalTheory.RealDict.LineStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittUnfoldedIntegralLeCoreQuotientHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.QuotUnfBound

variable {D : D7}

theorem unitaryAdelicHeight_wittEmbedding_le {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ g : GA D V₀, height V (d.emb0 g) ≤ C * height V₀ g := by
  obtain ⟨C, hC⟩ := GlobalTheory.EmbHeight.exists_heightGL_le D.host.F d.j0 d.p0 (d.jX ⬝ d.pX + d.jY ⬝ d.pY)
  refine ⟨max (C : ℝ) 1, le_max_right _ _, fun g => ?_⟩
  have h := hC (Formalism.L2.Theta.matHom V (d.emb0 g)) (Formalism.L2.Theta.matHom V₀ g) (by
      show Formalism.L2.Theta.mt V (d.emb0 g) = d.j0 ⬝ Formalism.L2.Theta.mt V₀ g ⬝ d.p0 + (d.jX ⬝ d.pX + d.jY ⬝ d.pY)
      rw [GlobalTheory.FlatRInv.unitaryMatrix_wittCoreEmbedding]; abel) (by
      rw [← map_inv, ← map_inv, ← map_inv]
      show Formalism.L2.Theta.mt V (d.emb0 g⁻¹) = d.j0 ⬝ Formalism.L2.Theta.mt V₀ g⁻¹ ⬝ d.p0 + (d.jX ⬝ d.pX + d.jY ⬝ d.pY)
      rw [GlobalTheory.FlatRInv.unitaryMatrix_wittCoreEmbedding]; abel)
  have h' : height V (d.emb0 g) ≤ (C : ℝ) * height V₀ g := by
    unfold GlobalTheory.Grow.height; exact_mod_cast h
  exact h'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (height_pos V₀ g).le)

theorem covolOne_lintegral_mul_right {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (ratMx D m n) μ 𝓕) (M M' : Mx D n n) (hM'M : M' ⬝ M = 1) (hMM' : M ⬝ M' = 1)
    (hM : M ∈ ratMx D n n) (hM' : M' ∈ ratMx D n n) (φ : Mx D m n → ℝ≥0∞)
    (hφ : ∀ γ ∈ ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫⁻ a in 𝓕, φ (a ⬝ M) ∂μ = ∫⁻ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let e : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => a ⬝ M
      invFun := fun a => a ⬝ M'
      left_inv := fun a => by simp only [Matrix.mul_assoc, hMM', Matrix.mul_one]
      right_inv := fun a => by simp only [Matrix.mul_assoc, hM'M, Matrix.mul_one]
      map_add' := fun a b => Matrix.add_mul _ _ _ }
  have he : Continuous e := continuous_id.matrix_mul continuous_const
  have he' : Continuous e.symm := continuous_id.matrix_mul continuous_const
  have hr : ∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n := fun x =>
    ⟨fun h => by
      have h2 := GlobalTheory.MixModel.ratMx_mul h hM'
      have h3 : e x ⬝ M' = x := e.symm_apply_apply x
      rwa [h3] at h2,
     fun h => GlobalTheory.MixModel.ratMx_mul h hM⟩
  obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hμ e he he' hr
  have hmeq : Measure.map e μ = μ := GlobalTheory.MixModel.covolOne_measure_eq hμ h1
  haveI := hμ.1
  have h1' := h1
  rw [hmeq] at h1'
  have hfd : ∫⁻ a in e '' 𝓕, φ a ∂μ = ∫⁻ a in 𝓕, φ a ∂μ :=
    h1'.2.1.setLIntegral_eq hμ.2.1 φ fun γ a => hφ γ γ.2 a
  have hmap : ∫⁻ a in e '' 𝓕, φ a ∂(Measure.map e μ) = ∫⁻ a in 𝓕, φ (e a) ∂μ := by
    rw [hemb.restrict_map, hemb.lintegral_map, Set.preimage_image_eq _ e.injective]
  calc ∫⁻ a in 𝓕, φ (a ⬝ M) ∂μ = ∫⁻ a in 𝓕, φ (e a) ∂μ := rfl
    _ = ∫⁻ a in e '' 𝓕, φ a ∂(Measure.map e μ) := hmap.symm
    _ = ∫⁻ a in e '' 𝓕, φ a ∂μ := by rw [hmeq]
    _ = ∫⁻ a in 𝓕, φ a ∂μ := hfd

theorem enorm_periodic {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V₀ W : HSp D} {ρ : ℕ}
    {F : WO V₀ W → ℂ} (hF : IsThetaFunO ψ V₀ W F) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    ∀ β ∈ ratMx D ρ V₀.rank, ∀ b, ‖F (rat x₀ ⬝ (β + b))‖ₑ = ‖F (rat x₀ ⬝ b)‖ₑ := by
  rintro _ ⟨β, rfl⟩ b
  show ‖F (rat x₀ ⬝ (rat β + b))‖ₑ = ‖F (rat x₀ ⬝ b)‖ₑ
  have e1 : rat x₀ ⬝ (rat β + b) = Formalism.L2.Theta.ratW W V₀ (x₀ ⬝ β) + rat x₀ ⬝ b := by
    rw [Matrix.mul_add]
    congr 1
    show (x₀.map (incA D)) ⬝ (β.map (incA D)) = (x₀ ⬝ β).map (incA D)
    rw [Matrix.map_mul]
  rw [e1, hF.quasi, enorm_mul, GlobalTheory.Unf.FlatForm.enorm_psi hψ, one_mul]

theorem inner_inv {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} {om' : Om V₀ W} (hW : IsWeilDatumO ψ V W χV χW om)
    (hW' : IsWeilDatumO ψ V₀ W χV χW om') (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank)
    (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) {Ψ : WO V W → ℂ} (hΨ : IsThetaFunO ψ V W Ψ) {γ : GA D V₀}
    (hγ : γ ∈ GQ V₀) (x : Mx D W.rank ρ) :
    ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 γ, 1) Ψ) x (rat x₀ ⬝ b)‖ₑ ∂vb.μ =
      ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 Ψ x (rat x₀ ⬝ b)‖ₑ ∂vb.μ := by
  set F := d.mixS W ψ vS.μ vS.𝓕 Ψ x with hFdef
  have hF : IsThetaFunO ψ V₀ W F := GlobalTheory.MixValues.mixS_theta D ψ hW.std V V₀ W ρ d vS.μ vS.𝓕 vS.covol Ψ hΨ x
  have hcore := (GlobalTheory.MixSourceFormulas.mixed_source D ψ V V₀ W ρ d χV χW om om' hW hW' vS.μ vS.𝓕 vS.covol Ψ hΨ).core γ x
  have hsub : ∀ w, d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 γ, 1) Ψ) x w = F (w ⬝ Formalism.L2.Theta.mt V₀ γ) := by
    intro w
    rw [hcore]
    have h := GlobalTheory.Unf.om_rat_mul D ψ V₀ W χV χW om' hW' F hF γ hγ 1 (one_mem _) 1 1 w
    rw [mul_one, mul_one, inv_one, show ((1 : GA D V₀), (1 : GA D W)) = 1 from rfl, map_one] at h
    rw [h]
    simp [Formalism.L2.Theta.mt]
  have hM := (GlobalTheory.MixModel.mem_GQ_iff V₀ γ).1 hγ
  have hM' := (GlobalTheory.MixModel.mem_GQ_iff V₀ γ⁻¹).1 (inv_mem hγ)
  have h1 : Formalism.L2.Theta.mt V₀ γ⁻¹ ⬝ Formalism.L2.Theta.mt V₀ γ = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]; exact Units.inv_mul _
  have h2 : Formalism.L2.Theta.mt V₀ γ ⬝ Formalism.L2.Theta.mt V₀ γ⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]; exact Units.mul_inv _
  have hmul : ∀ b : Mx D ρ V₀.rank, rat x₀ ⬝ b ⬝ Formalism.L2.Theta.mt V₀ γ = rat x₀ ⬝ (b ⬝ Formalism.L2.Theta.mt V₀ γ) :=
    fun b => Matrix.mul_assoc _ _ _
  simp_rw [hsub, hmul]
  exact covolOne_lintegral_mul_right vb.covol (Formalism.L2.Theta.mt V₀ γ) (Formalism.L2.Theta.mt V₀ γ⁻¹) h1 h2 hM hM'
    (fun b => ‖F (rat x₀ ⬝ b)‖ₑ) (enorm_periodic hW.std hF x₀)

theorem unfolded_rat_inv {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} {om' : Om V₀ W} (hW : IsWeilDatumO ψ V W χV χW om)
    (hW' : IsWeilDatumO ψ V₀ W χV χW om') (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ)
    (vW : GlobalTheory.Unf.Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) {Φ : WO V W → ℂ}
    (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W)) {γ : GA D V₀} (hγ : γ ∈ GQ V₀) (g : GA D V₀) :
    ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 (γ * g), h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ =
      ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ := by
  refine lintegral_congr fun h => ?_
  congr 1
  refine lintegral_congr fun u => ?_
  have e : om (d.emb0 (γ * g), h) Φ = om (d.emb0 γ, 1) (om (d.emb0 g, h) Φ) := by
    rw [map_mul, show ((d.emb0 γ * d.emb0 g, h) : GA D V × GA D W) = (d.emb0 γ, 1) * (d.emb0 g, h) by
      simp [Prod.mk_mul_mk], map_mul]
    rfl
  rw [e]
  exact inner_inv d hW hW' vS vb x₀ (hW.om_pres _ Φ hΦ) hγ _

end GlobalTheory.QuotUnfBound

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : GlobalTheory.Unf.Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤ ENNReal.ofReal (C * quotHeight V₀ g ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om hW vS vb vU vW x₀ hx G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨om', hW'⟩ :=
    ((GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)) ψ V W χV χW om hW).1 V₀ ρ d
  obtain ⟨C, A, hC⟩ := GlobalTheory.Unf.UnfoldBound.unfolded_integral_le D ψ V V₀ W ρ d χV χW om om' hW hW' vS vb vU vW x₀ hx G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨C₁, hC₁1, hC₁⟩ := GlobalTheory.QuotUnfBound.unitaryAdelicHeight_wittEmbedding_le d
  have hM : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
  have hKpos : (0 : ℝ) < max C 1 * C₁ ^ A := mul_pos hM (pow_pos (one_pos.trans_le hC₁1) A)
  refine ⟨max C 1 * C₁ ^ A, A, fun g => ?_⟩
  have hb : ∀ k : GA D V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 k, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤
        ENNReal.ofReal (max C 1 * C₁ ^ A) * ENNReal.ofReal (height V₀ k ^ A) := by
    intro k
    rw [← ENNReal.ofReal_mul hKpos.le]
    refine (hC (d.emb0 k)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h0 : 0 ≤ height V (d.emb0 k) := (height_pos V _).le
    have h1 : height V (d.emb0 k) ^ A ≤ (C₁ * height V₀ k) ^ A := pow_le_pow_left₀ h0 (hC₁ k) A
    calc C * height V (d.emb0 k) ^ A ≤ max C 1 * height V (d.emb0 k) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 A)
      _ ≤ max C 1 * (C₁ * height V₀ k) ^ A := mul_le_mul_of_nonneg_left h1 hM.le
      _ = max C 1 * C₁ ^ A * height V₀ k ^ A := by rw [mul_pow, mul_assoc]
  have hle : ∀ γ : GQ V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤
        ENNReal.ofReal (max C 1 * C₁ ^ A) * ENNReal.ofReal (height V₀ ((γ : GA D V₀) * g) ^ A) := by
    intro γ
    rw [← GlobalTheory.QuotUnfBound.unfolded_rat_inv d hW hW' vS vb vU vW x₀ G hΦ 𝓑 γ.2 g]
    exact hb _
  rw [ENNReal.ofReal_mul hKpos.le, GlobalTheory.MixSumBound.ofReal_quotHeight_pow,
    ENNReal.mul_iInf_of_ne (by simpa using hKpos) ENNReal.ofReal_ne_top]
  exact le_iInf hle

end
end

