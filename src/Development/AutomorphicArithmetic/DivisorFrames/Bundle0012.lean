import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0001
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0009
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0010
import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0002
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.StdSectionSecondEqProdLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical in
private theorem stdB_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (Y : Matrix (Fin a') (Fin (a + a')) k) :
    GlobalTheory.StdPairCone.stdB ν ϖ c a a' Y =
      if (∀ i j, Y i (Fin.natAdd a j) ∈ 𝒪[k]) ∧ ∀ i j, Y i (Fin.castAdd a' j) ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
        GlobalTheory.StdPairCone.unitInd ν (GlobalTheory.StdPairCone.blk₂ Y).det else 0 := by
  unfold GlobalTheory.StdPairCone.stdB GlobalTheory.StdPairCone.unitInd
  split_ifs with h1 h2 h3 h4 h5
  · rfl
  · exact absurd ⟨h1.1, h1.2.1.2⟩ h3
  · exact absurd ⟨h1.2.1.1, h1.2.2⟩ h2
  · exact absurd ⟨h5.1, ⟨h4.1, h5.2⟩, h4.2⟩ h1
  · rfl
  · rfl

private theorem cA_invol {D : D7} (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

private theorem half_alg {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (e : R) (x : S) {m n : ℕ}
    (P : Matrix (Fin m) (Fin m) S) (G : Matrix (Fin m) (Fin m) R) (M : Matrix (Fin m) (Fin n) R)
    (H : Matrix (Fin n) (Fin n) R) (Q : Matrix (Fin n) (Fin n) S) (h : e • M = M) (i : Fin m) (j : Fin n) :
    f e * (x • (P * (G * M * H).map f * Q)) i j = (x • (P * (G * M * H).map f * Q)) i j := by
  have h1 : f e • (G * M * H).map f = (G * M * H).map f := by
    conv_rhs => rw [← h, Matrix.mul_smul, Matrix.smul_mul]
    ext i j
    exact (RingHom.map_mul f e _).symm
  have h2 : f e • (x • (P * (G * M * H).map f * Q)) = x • (P * (G * M * H).map f * Q) := by
    rw [smul_comm, ← Matrix.smul_mul (f e), ← Matrix.mul_smul P (f e), h1]
  exact congrFun (congrFun h2 i) j

private theorem dualCoord_half {D : D7} (ε : AE D) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (y : WO A' WW) (hy : IsHalf (cA D ε) y) (i : Fin A'.rank) (j : Fin WW.rank) :
    toEAf D ε * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y i j = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y i j := by
  refine half_alg (toEAf D) ε _ _ _ _ _ _ ?_ i j
  ext i j
  have := congrArg (cA D) (hy j i)
  rw [RingHom.map_mul, cA_invol] at this
  exact this

private theorem cball_sub {F : Type} [Field F] [NumberField F] (v : Pl F) (c : ℕ) (x : Fv F v)
    (hx : x ∈ GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ c)) : x ∈ 𝒪[Fv F v] := by
  have h : valuation (Fv F v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  rw [Valuation.mem_integer_iff]
  refine le_trans (show valuation (Fv F v) x ≤ valuation (Fv F v) ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ c : (Fv F v)ˣ) : Fv F v)
    from hx) ?_
  rw [Units.val_pow_eq_pow_val, map_pow, h]
  exact pow_le_one₀ zero_le' uniformizer_lt_one.le

open Classical in
private theorem core (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)) (hε : IsIdemSum ε Pw) (ι : Type) [Fintype ι]
    (pl : ι → Pl D.host.F) (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i))
    (hP : ∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) (hinj : Function.Injective (fun i => splitPrime (τ i)))
    (c : Pl D.host.E → ℕ) (ν : (AE D)ˣ →* Circle) (a k d : ℕ) (hk : a + k = d)
    (Y : Matrix (Fin k) (Fin d) (Lev.EAf D)) (hY : ∀ i j, toEAf D ε * Y i j = Y i j) :
    (if IsIntM Y ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) (Y i j) then
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a Y) else 0) =
      ∏ i, GlobalTheory.StdPairCone.stdB (chrW ν (τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i)) (c (splitPrime (τ i))) a k
        ((Y.map (GlobalTheory.BotMatch.evW (τ i))).submatrix id (finCongr hk)) := by
  subst hk
  have hI := fun i j => UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings D ε Pw hε ι pl τ hP hinj c (Y i j) (hY i j)
  have hb : ∀ l, GlobalTheory.StdPairCone.blk₂ ((Y.map (GlobalTheory.BotMatch.evW (τ l))).submatrix id (finCongr rfl)) =
      (GlobalTheory.BotMatch.evW (τ l)).mapMatrix (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a Y) := fun l => by
    funext i j
    have h : a + j.1 < a + k := by omega
    show _ = GlobalTheory.BotMatch.evW (τ l) (if h : a + j.1 < a + k then Y i ⟨a + j.1, h⟩ else 0)
    rw [dif_pos h]
    rfl
  simp only [stdB_eq, hb, ← RingHom.map_det]
  by_cases h : IsIntM Y ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) (Y i j)
  · rw [if_pos h, UpperTheory.unitChar_idempotentSum_eq_prod_unitInd D ε Pw hε ι pl τ hP hinj ν k]
    · refine Finset.prod_congr rfl fun l _ => (if_pos ⟨fun i j => ?_, fun i j => ?_⟩).symm
      · exact (hI i _).1.1 (h.1 i _) l
      · exact (hI i _).2.1 (h.2 i (Fin.castAdd k j) j.2) l
    · intro l
      rw [RingHom.map_det, ← hb, Matrix.det_apply']
      refine sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => ?_)
      exact (hI _ _).1.1 (h.1 _ _) l
  · rw [if_neg h]
    symm
    by_contra hne
    have hall : ∀ l, (∀ i j, GlobalTheory.BotMatch.evW (τ l) (Y i (Fin.natAdd a j)) ∈ 𝒪[Fv D.host.F (pl l)]) ∧
        ∀ i j, GlobalTheory.BotMatch.evW (τ l) (Y i (Fin.castAdd k j)) ∈
          GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl l) ^ c (splitPrime (τ l))) := fun l => by
      by_contra hl
      exact hne (Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl))
    refine h ⟨fun i j => (hI i j).1.2 fun l => ?_, fun i j hj => (hI i j).2.2 fun l => (hall l).2 i ⟨j.1, hj⟩⟩
    induction j using Fin.addCases with
    | left j => exact cball_sub _ _ _ ((hall l).2 i j)
    | right j => exact (hall l).1 i j

theorem UpperTheory.stdSectionSecond_eq_prod_local :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (c : Pl D.host.E → ℕ) (ν : (AE D)ˣ →* Circle) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (Lev.EAf D))
          (βW : GL (Fin WW.rank) (Lev.EAf D)) (hk : a + A'.rank = WW.rank) (y : WO A' WW), IsHalf (cA D ε) y →
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν ε (∏ w ∈ Pw, w.asIdeal ^ c w) a A' WW βA' βW y =
            ∏ i, GlobalTheory.StdPairCone.stdB (chrW ν (τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i)) (c (splitPrime (τ i))) a A'.rank
              (((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (GlobalTheory.BotMatch.evW (τ i))).submatrix id (finCongr hk)) := by
  intro D ε Pw hε ι _ pl τ hP hinj c ν a A' WW βA' βW hk y hy
  classical
  rw [← core D ε Pw hε ι pl τ hP hinj c ν a A'.rank WW.rank hk _ (dualCoord_half ε A' WW βA' βW y hy)]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
  simp only [hy, true_and]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ThetaLiftPureTensorOfIsFinF
section
section SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At evI realAd SInf ActsD piInf Spc Model)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealDict GlobalTheory.RealDict.FockMap

private theorem finPart_ne {F : Type} [Field F] [NumberField F] {n d : ℕ}
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y, GlobalTheory.BigNZ.finPartFn φ y ≠ 0 := by
  classical
  choose ξ hξ using fun v => Function.ne_iff.1 (h0 v)
  have hS := Filter.eventually_cofinite.1 hs
  let y : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)
  refine ⟨y, ?_⟩
  refine finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
  by_cases hv : v ∈ hS.toFinset
  · have : (fun k => evalV F v (y k)) = ξ v := funext fun k => by
      rw [map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]
    rw [this]
    exact hξ v
  · have : (fun k => evalV F v (y k)) = 0 := funext fun k => by
      rw [map_sum]
      exact Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _
    rw [this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]
    exact one_ne_zero

set_option maxHeartbeats 1000000 in

private theorem fock_of {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {M X : HSp D} {Xs : Spc D.host.F D.host.E M.rank}
    {Ws : Spc D.host.F D.host.E X.rank} (Mo : Model D.sp.cm.sig Xs Ws)
    (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr M) (B : Fr X)
    {τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w} (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig)
    (hStd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hX : Xs.J = sgE (D := D) ε • M.gram)
    (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (hM : Mo.IsGood ψ) (h2X : ∀ w, Xs.θ w * Xs.θ w = 1) (h2W : ∀ w, Ws.θ w * Ws.θ w = 1)
    (hc : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
      Ws.θ w = (B.cart t).map conj)
    (g₀ : SInf D.host.F (Fin M.rank × Fin X.rank)) (g0 : g₀ ≠ 0)
    {g : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ} (hg : g ∈ SB _) (hy : ∃ y, g y ≠ 0)
    (hv : IsVacF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g))) :
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank),
      LinearMap.range Φ = Mo.Pol ψ τ ∧
      ∀ g' : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ, g' ∈ SB _ →
        ∀ P, th ψ ε Mo (pureA D.host.F (Φ P) g') = ptF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g')) P := by
  obtain ⟨-, -, tinj, tth, -⟩ := th_laws Mo hψ hθ hX hW hM
  obtain ⟨Dr, hD1, hD2, hD3⟩ := exists_der Mo hStd
  obtain ⟨y, hy⟩ := hy
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = thL Mo hψ hθ hX hW hM hg := ⟨_, rfl⟩
  have hΘ' : ∀ f : SInf D.host.F (Fin M.rank × Fin X.rank), th ψ ε Mo (pureA D.host.F f g) = Θ f := fun f => by rw [hΘ]; rfl
  rw [hΘ'] at hv
  have hd : ∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f) :=
    hΘ ▸ dRho_thL Mo hψ hθ hX hW hM hD1 hg
  have hi : Function.Injective Θ := fun f f' h => by
    have e := tinj _ (pureA_mem f hg) _ (pureA_mem f' hg) (by rw [hΘ] at h; exact h)
    refine DFunLike.ext _ _ fun a => ?_
    have e2 := congrFun e (GlobalTheory.RealLift.ptAt a y)
    rw [GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt] at e2
    exact mul_right_cancel₀ hy e2
  have hg₀ : ∀ t z, Dr (dir ε M X θ t z) g₀ +
      Complex.I • Dr (dir ε M X θ t (cplxO ((frSgn ε A).cart t) (B.cart t) z)) g₀ = 0 := fun t z => hi (by
    have h : annih (heisO ψ (sgn ε M) X) θ t (cplxO ((frSgn ε A).cart t) (B.cart t)) z (Θ g₀) = 0 := hv.2 t z
    rw [annih, hd, hd, ← map_smul, ← map_add] at h
    rw [h, map_zero])
  let um : FVar D X.rank M.rank → Matrix (Fin X.rank) (Fin M.rank) ℂ := fun k =>
    Formalism.IndefR.Datum.unitMap ((frSgn ε A).onb k.1) (B.onb k.1) k.2.1 k.2.2
  let Cr : FVar D X.rank M.rank → SInf D.host.F (Fin M.rank × Fin X.rank) → SInf D.host.F (Fin M.rank × Fin X.rank) :=
    fun k f => ((fockScale D k.1 : ℂ)⁻¹) • (Dr (dir ε M X θ k.1 (um k)) f -
      Complex.I • Dr (dir ε M X θ k.1 (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (um k))) f)
  let Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank) :=
    (MvPolynomial.basisMonomials _ ℂ).constr ℂ fun k => (Multiset.toList (Finsupp.toMultiset k)).foldr Cr g₀
  have hΦ : ∀ Θ : SInf D.host.F (Fin M.rank × Fin X.rank) →ₗ[ℂ] (WO (sgn ε M) X → ℂ),
      (∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f)) →
      Θ ∘ₗ Φ = pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart (frSgn ε A).onb B.onb (Θ g₀) := by
    intro Θ hd
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.comp_apply, pureTensorO, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis, opPow]
    induction (Finsupp.toMultiset k).toList with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih, aPlusAll, Formalism.IndefR.Datum.aPlus, crea, hd, hd, ← map_smul, ← map_sub,
        ← map_smul]
  have hΦ' : ∀ P, Θ (Φ P) = ptF ψ θ (frSgn ε A) B (Θ g₀) P := fun P => LinearMap.congr_fun (hΦ Θ hd) P
  have hsum : ∀ u, At (evI D.host.F) u → ∀ f, Dr u f =
      ∑ t, Dr (dir ε M X θ t (compAt θ t (toO (sgn ε M).gram u))) f := fun u hu f => by
    rw [← hD3 _ _ _ fun t => dir_at hθ t _, ← eq_sum_dir hθ hu]
  have hG : Mo.IsGauss ψ τ g₀ := ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => by
    rw [hD2 u hu _ _ hf, hD2 u' hu' _ _ hf', hsum u hu, hsum u' hu', Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [compAt_cplx hθ A B hc (fun w => by simpa using hrel w) t,
      eq_neg_of_add_eq_zero_left (hg₀ t (compAt θ t (toO (sgn ε M).gram u))), smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]⟩
  have hP : ∀ u, At (evI D.host.F) u → ∀ f ∈ Mo.Pol ψ τ, Dr u f ∈ Mo.Pol ψ τ := fun u hu f hf =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (hD1 u hu f)
  refine ⟨Φ, le_antisymm ?_ (sInf_le ⟨fun f hf => ?_, ?_⟩), fun g' hg' P =>
    LinearMap.congr_fun (hΦ (thL Mo hψ hθ hX hW hM hg') (dRho_thL Mo hψ hθ hX hW hM hD1 hg')) P⟩
  · rw [Module.Basis.constr_range, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    beta_reduce
    induction (Finsupp.toMultiset k).toList with
    | nil => exact Submodule.mem_sInf.2 fun N hN => hN.1 g₀ hG
    | cons i l ih =>
      exact Submodule.smul_mem _ _ (sub_mem (hP _ (dir_at hθ _ _) _ ih) (Submodule.smul_mem _ _ (hP _ (dir_at hθ _ _) _ ih)))
  · obtain ⟨z, rfl⟩ := gauss_line Mo ψ τ hCM hStd h2X h2W f g₀ hG g0 hf
    exact Submodule.smul_mem _ z ⟨1, hi ((hΦ' 1).trans (GlobalTheory.LieScalar.ptF_one _ _ _))⟩
  · rintro u hu _ ⟨P, rfl⟩ f₁ h1
    rw [hD2 u hu _ _ h1, hsum u hu]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨Q, hQ⟩ := dRho_ptF (frSgn ε A) B hψ hθ hv t (compAt θ t (toO (sgn ε M).gram u)) P
    exact ⟨Q, hi (by rw [← hd, hΦ', hΦ', hQ])⟩

end SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.thetaLift_pure_tensor_of_isFinF :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (hd : d = X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X (finCongr hd) Bs Vs Ws M → ∀ (θ : InfFam D), IsInfFam θ →
        ∀ (A : Fr S) (B : Fr X), IsCart ε A B (finCongr hd) Bs Vs Ws →
        ∀ (g : SInf D.host.F (Fin S.rank × Fin d)), g ≠ 0 →
        ∀ (φ₀ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ), (∀ v, φ₀ v ∈ GlobalTheory.WeilM.SB _) →
        (∀ᶠ v in Filter.cofinite, φ₀ v = M.vac v) → (∀ v, φ₀ v ≠ 0) →
        IsFinF ψ θ ε A B (thO M ψ (sgn ε S).gram (finCongr hd) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ₀)) →
        ∃ Φ : PolF D X.rank S.rank →ₗ[ℂ] SInf D.host.F (Fin S.rank × Fin d), LinearMap.range Φ = M.Pol Bs.ψ Bs.emb ∧
          ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
            (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ P,
            thO M ψ (sgn ε S).gram (finCongr hd) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
              fockF ψ θ ε A B (thO M ψ (sgn ε S).gram (finCongr hd) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) P := by
  intro D ψ ε S X d hd Bs Vs Ws M hP θ hθ A B hc g g0 φ₀ hφ hφ' hφ0 hv
  subst hd
  obtain ⟨hBs, hψe, hX, hW, ⟨r, s, hV⟩, ⟨r', s', hWs⟩, hM⟩ := hP
  subst hψe
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hBs.std
  have hF : GlobalTheory.BigNZ.Fam M φ₀ := ⟨hφ, hφ'⟩
  obtain ⟨Φ, h1, h2⟩ := fock_of M hψ hθ A B hBs.cm hBs.std hX hW hM (fun w => (hV.cartan w).1)
    (fun w => (hWs.cartan w).1) hc g g0 (hF.sb hM) (finPart_ne φ₀ hφ0 (hF.std hM)) hv
  refine ⟨Φ, h1, fun φ hs hs' P => ?_⟩
  have hF' : GlobalTheory.BigNZ.Fam M φ := ⟨hs, hs'⟩
  exact h2 _ (hF'.sb hM) P
end

