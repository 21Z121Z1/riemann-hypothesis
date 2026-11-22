import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ThetaTransformFockModelEqOfStandardChar
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
      ∀ P, th ψ ε Mo (pureA D.host.F (Φ P) g) = ptF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g)) P := by
  obtain ⟨-, -, tinj, tth, -⟩ := th_laws Mo hψ hθ hX hW hM
  obtain ⟨Dr, hD1, hD2, hD3⟩ := exists_der Mo hStd
  obtain ⟨y, hy⟩ := hy
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = thL Mo hψ hθ hX hW hM hg := ⟨_, rfl⟩
  have hΘ' : ∀ f : SInf D.host.F (Fin M.rank × Fin X.rank), th ψ ε Mo (pureA D.host.F f g) = Θ f := fun f => by rw [hΘ]; rfl
  rw [hΘ'] at hv
  simp only [hΘ']
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
  have hΦ : Θ ∘ₗ Φ = pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart (frSgn ε A).onb B.onb (Θ g₀) := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.comp_apply, pureTensorO, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis, opPow]
    induction (Finsupp.toMultiset k).toList with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih, aPlusAll, Formalism.IndefR.Datum.aPlus, crea, hd, hd, ← map_smul, ← map_sub,
        ← map_smul]
  have hΦ' : ∀ P, Θ (Φ P) = ptF ψ θ (frSgn ε A) B (Θ g₀) P := fun P => LinearMap.congr_fun hΦ P
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
  refine ⟨Φ, le_antisymm ?_ (sInf_le ⟨fun f hf => ?_, ?_⟩), hΦ'⟩
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.theta_transform_fock_model_eq_of_standard_char :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
        ∀ (ε : Bool) (M X : HSp D) (k : ℕ) (hk : k = X.rank) (Xs : Spc D.host.F D.host.E M.rank) (Ws : Spc D.host.F D.host.E k)
        (Mo : Model D.sp.cm.sig Xs Ws), Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram →
        Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (finCongr hk) (finCongr hk) → Mo.IsGood ψ →
        ∀ (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w),
        (∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
          Ws.θ w = ((B.cart t).submatrix (finCongr hk) (finCongr hk)).map conj) →
        ∀ (f₀ : SInf D.host.F (Fin M.rank × Fin k)) (φ : ∀ v : Pl D.host.F, (Fin M.rank × Fin k → Fv D.host.F v) → ℂ), f₀ ≠ 0 →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Mo.vac v) → (∀ v, φ v ≠ 0) →
        GlobalTheory.SquareComm.IsFinF ψ θ ε A B (GlobalTheory.TripleRead.thO Mo ψ (GlobalTheory.Grid.sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ)) →
        ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin k), LinearMap.range Φ = Mo.Pol ψ τ ∧
          ∀ P, GlobalTheory.TripleRead.thO Mo ψ (GlobalTheory.Grid.sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
            GlobalTheory.SquareComm.fockF ψ θ ε A B
              (GlobalTheory.TripleRead.thO Mo ψ (GlobalTheory.Grid.sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ)) P := by
  intro D ψ θ hψ hθ ε M X k hk Xs Ws Mo hX hW hM A B τ hc f₀ φ hf hφ hφ' hφ0 hv
  subst hk
  have hF : GlobalTheory.BigNZ.Fam Mo φ := ⟨hφ, hφ'⟩
  have h2X : ∀ w, Xs.θ w * Xs.θ w = 1 := fun w => by
    obtain ⟨t, -, h, -⟩ := hc w
    rw [h, Matrix.smul_mul, Matrix.mul_smul, (GlobalTheory.ChainFr.Model.isCartanInv_cart A t).1, smul_smul]
    cases ε <;> simp
  have h2W : ∀ w, Ws.θ w * Ws.θ w = 1 := fun w => by
    obtain ⟨t, -, -, h⟩ := hc w
    have h' : Ws.θ w = (B.cart t).map (starRingEnd ℂ) := h
    rw [h', ← Matrix.map_mul, (GlobalTheory.ChainFr.Model.isCartanInv_cart B t).1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact fock_of Mo hψ hθ A B (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) hX hW hM h2X h2W hc
    f₀ hf (hF.sb hM) (finPart_ne φ hφ0 (hF.std hM)) hv
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.UnitCharIdempotentSumEqProdUnitInd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cpt_finAd {D : D7} (Q : Pl D.host.E) (z : AE D) :
    cpt (D := D) Q (toEAf D z) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D z) Q := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero, RingEquiv.map_zero]; rfl
  | tmul a x =>
    have h1 := congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q) (toAd_spec D x a.2)
    have h2 := congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q)
      ((GlobalTheory.LFun.toFinAd_tmul (F := D.host.F) a.2 x).trans (mul_comm _ _))
    exact h1.trans h2.symm
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingEquiv.map_add, ha, hb]; rfl

private theorem cpt_loc {D : D7} (w Q : Pl D.host.E) (y : (Kw w)ˣ) :
    cpt (D := D) Q (toEAf D (GlobalTheory.LFun.locIdele D.host.F w y : AE D)) =
      (Neutral.B1.finiteSingle D.host.E w (y : Kw w)) Q := by
  rw [cpt_finAd]
  exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y)

open Classical in
private theorem cpt_sum {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt (D := D) Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  rw [hsum, map_sum (toEAf D), map_sum (cpt (D := D) Q)]
  split_ifs with hQ
  · rw [Finset.sum_eq_single Q (fun P hP hPQ => (cpt_of_isIdemAt (hes P hP)).2 Q (Ne.symm hPQ))
      (fun h => absurd hQ h)]
    exact (cpt_of_isIdemAt (hes Q hQ)).1
  · exact Finset.sum_eq_zero fun P hP => (cpt_of_isIdemAt (hes P hP)).2 Q (fun h => hQ (h ▸ hP))

private theorem cpt_prod {D : D7} {ι : Type} [Fintype ι] (w : ι → Pl D.host.E) (hw : Function.Injective w)
    (y : ∀ i, (Kw (w i))ˣ) :
    infPart D ((∏ i, GlobalTheory.LFun.locIdele D.host.F (w i) (y i) : (AE D)ˣ) : AE D) = 1 ∧
    (∀ i, cpt (D := D) (w i) (toEAf D ((∏ i, GlobalTheory.LFun.locIdele D.host.F (w i) (y i) : (AE D)ˣ) : AE D)) = y i) ∧
    ∀ Q, (∀ i, w i ≠ Q) → cpt (D := D) Q (toEAf D ((∏ i, GlobalTheory.LFun.locIdele D.host.F (w i) (y i) : (AE D)ˣ) : AE D)) = 1 := by
  refine ⟨?_, fun i => ?_, fun Q hQ => ?_⟩
  · rw [Units.coe_prod, map_prod (infPart D)]
    exact Finset.prod_eq_one fun i _ => GlobalTheory.LFun.infTens_locIdele (F := D.host.F) (w i) _
  · rw [Units.coe_prod, map_prod (toEAf D), map_prod (cpt (D := D) _), Finset.prod_eq_single i]
    · rw [cpt_loc, GlobalTheory.LFun.finSingle_self]
    · intro b _ hb
      rw [cpt_loc]
      exact GlobalTheory.LFun.finSingle_ne (fun h => hb (hw h).symm) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Units.coe_prod, map_prod (toEAf D), map_prod (cpt (D := D) _)]
    exact Finset.prod_eq_one fun i _ => by
      rw [cpt_loc]
      exact GlobalTheory.LFun.finSingle_ne (hQ i).symm _

private theorem valued_evW {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : Lev.EAf D) :
    Valued.v (GlobalTheory.BotMatch.evW τ z) = Valued.v (cpt (D := D) (splitPrime τ) z) := by
  rw [← GlobalTheory.BotMatch.complEquiv_evW, complEquiv_apply, SplitTie.valued_complMap]

theorem UpperTheory.unitChar_idempotentSum_eq_prod_unitInd :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (ν : (AE D)ˣ →* Circle) (n : ℕ) (N : Matrix (Fin n) (Fin n) (Lev.EAf D)),
          (∀ i, GlobalTheory.BotMatch.evW (τ i) N.det ∈ 𝒪[Fv D.host.F (pl i)]) →
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν ε N = ∏ i, GlobalTheory.StdPairCone.unitInd (chrW ν (τ i)) (GlobalTheory.BotMatch.evW (τ i) N.det) := by
  intro D ε Pw hε ι _ pl τ hPw hinj ν n N hN
  classical
  have hc : ∀ Q, cpt (D := D) Q (1 - toEAf D ε + toEAf D ε * N.det) = if Q ∈ Pw then cpt (D := D) Q N.det else 1 := by
    intro Q
    rw [RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, cpt_sum hε]
    split_ifs <;> simp
  by_cases h : ∀ i, GlobalTheory.BotMatch.evW (τ i) N.det ≠ 0 ∧ valuation (Fv D.host.F (pl i)) (GlobalTheory.BotMatch.evW (τ i) N.det) = 1
  · let y : ∀ i, (Kw (D := D) (splitPrime (τ i)))ˣ := fun i =>
      Units.map (complMap (splitPrime_under (τ i))).toMonoidHom (Units.mk0 _ (h i).1)
    have hy : ∀ i, (y i : Kw (D := D) (splitPrime (τ i))) = cpt (D := D) (splitPrime (τ i)) N.det := fun i =>
      GlobalTheory.BotMatch.complEquiv_evW (τ i) N.det
    have hv : ∀ i, Valued.v (y i : Kw (D := D) (splitPrime (τ i))) = 1 := fun i => by
      rw [hy, ← valued_evW]
      exact (GlobalTheory.FlipMatch.isEquiv_Fv (pl i)).eq_one_iff_eq_one.1 (h i).2
    obtain ⟨x, hx⟩ : ∃ x : (AE D)ˣ, x = ∏ i, GlobalTheory.LFun.locIdele D.host.F (splitPrime (τ i)) (y i) := ⟨_, rfl⟩
    obtain ⟨h1, h2, h3⟩ := cpt_prod (fun i => splitPrime (τ i)) hinj y
    obtain ⟨-, h5, h6⟩ := cpt_prod (fun i => splitPrime (τ i)) hinj (fun i => (y i)⁻¹)
    have hxi : x⁻¹ = ∏ i, GlobalTheory.LFun.locIdele D.host.F (splitPrime (τ i)) (y i)⁻¹ := by
      rw [hx, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => (map_inv _ _).symm
    rw [← hx] at h1 h2 h3
    rw [← hxi] at h5 h6
    have hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet ε N x := by
      refine ⟨h1, cpt_ext fun Q => ?_, (mem_OA_iff _).2 fun Q => ?_⟩
      · rw [hc]
        split_ifs with hQ
        · obtain ⟨i, rfl⟩ := (hPw Q).1 hQ
          exact (h2 i).trans (hy i)
        · exact h3 Q fun i hi => hQ ((hPw Q).2 ⟨i, hi⟩)
      · by_cases hQ : ∃ i, splitPrime (τ i) = Q
        · obtain ⟨i, rfl⟩ := hQ
          rw [h5 i, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
        · rw [h6 Q fun i hi => hQ ⟨i, hi⟩]
          exact one_mem _
    have hex : ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet ε N x := ⟨x, hU⟩
    have he : hex.choose = x := Units.ext (ae_ext (hex.choose_spec.1.trans hU.1.symm) fun Q => by
      rw [hex.choose_spec.2.1, hU.2.1])
    rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar, dif_pos hex, he, hx, map_prod ν, ← Finset.prod_inv_distrib]
    refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
    rw [GlobalTheory.StdPairCone.unitInd, dif_pos (h i)]
    rfl
  · obtain ⟨i, hi⟩ := not_forall.1 h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [GlobalTheory.StdPairCone.unitInd, dif_neg hi]),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar, dif_neg]
    rintro ⟨x, -, h2, h3⟩
    apply hi
    have h4 := (mem_OA_iff _).1 h3 (splitPrime (τ i))
    have h5 : cpt (D := D) (splitPrime (τ i)) (toEAf D (x : AE D)) = cpt (D := D) (splitPrime (τ i)) N.det := by
      rw [h2, hc, if_pos ((hPw _).2 ⟨i, rfl⟩)]
    have h6 : cpt (D := D) (splitPrime (τ i)) N.det * cpt (D := D) (splitPrime (τ i)) (toEAf D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← h5, ← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one]
    have h7 : Valued.v (cpt (D := D) (splitPrime (τ i)) N.det) ≤ 1 := by
      rw [← valued_evW]
      exact (GlobalTheory.FlipMatch.isEquiv_Fv (pl i)).le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 (hN i))
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h4
    have h8 := congrArg Valued.v h6
    rw [map_mul, map_one] at h8
    have h9 : Valued.v (GlobalTheory.BotMatch.evW (τ i) N.det) = 1 := by
      rw [valued_evW]
      exact le_antisymm h7 (h8 ▸ mul_le_of_le_one_right' h4)
    exact ⟨fun h0 => by rw [h0, map_zero] at h9; exact zero_ne_one h9,
      (GlobalTheory.FlipMatch.isEquiv_Fv (pl i)).eq_one_iff_eq_one.2 h9⟩
end

