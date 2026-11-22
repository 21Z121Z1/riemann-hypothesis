import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellMultiplicityPositiveCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0740
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0718
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0744
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFrameUnitaryDivisorSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameOff

noncomputable def evAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem map_conj_eq_one {R S : Type} [CommRing R] [CommRing S] {m k : ℕ} (f : R →+* S) (b : Matrix (Fin m) (Fin k) R)
    (b' : Matrix (Fin k) (Fin m) R) (K : Matrix (Fin k) (Fin k) R) (hb : b * b' = 1) (hK : K.map f = 1) :
    (b * K * b').map f = 1 := by
  rw [Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, hb, Matrix.map_one _ (map_zero f) (map_one f)]

set_option maxHeartbeats 1000000 in

theorem evAt_swapCast_symm (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (x : ReciprocityTheory.Aut.AL D.host.E) :
    evAt D v ((swapCast hF).symm x) =
      (Algebra.TensorProduct.comm (maximalRealSubfield D.host.E) D.host.E (v.adicCompletion (maximalRealSubfield D.host.E)))
        (ReciprocityTheory.Aut.compAt D.host.E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingEquiv.map_zero, RingHom.map_zero, RingHom.map_zero, _root_.map_zero]
  | tmul e a => rfl
  | add x y hx hy => rw [RingEquiv.map_add, RingHom.map_add, RingHom.map_add, _root_.map_add, hx, hy]

theorem map_evAt_eq_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) {n : ℕ}
    (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (κ : Formalism.AUTREP.GAf D.host.E n) (hA : ReciprocityTheory.Aut.TrivOutside A κ) (hv : v ∉ A) :
    ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (swapCast hF).symm).map (evAt D v) = 1 := by
  have h1 := hA v hv
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  rw [Matrix.map_apply] at h2
  rw [Matrix.map_apply, Matrix.map_apply, evAt_swapCast_symm, h2]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

theorem stdFrame_stab_red : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, finE V (P.ψ κ) ∈ Formalism.L2.DIV.St β ∧ ∀ (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (PP : Formalism.L2.DIV.Pl D.host.E), ReciprocityTheory.Aut.TrivOutside A κ → NG.OverPl PP v → v ∉ A → redFn β PP (finE V (P.ψ κ)) = 1 := by
  intro D V n hF P β Λ hP hB κ hκ
  have hSt : finE V (P.ψ κ) ∈ Formalism.L2.DIV.St β :=
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hκ)
  refine ⟨hSt, fun A v PP hA hPP hv => ?_⟩
  have hu : PP.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPP
  refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt ?_
  rw [GlobalTheory.FinPl.KOpen.proj_eq_one_iff, hu]
  obtain ⟨⟨b, b', hbb, -, hmat⟩, -⟩ := hP
  have hF1 : (finMat D.sp.cm.sig V.gram (P.ψ κ)).map (evAt D v) = 1 := by
    rw [hmat κ]
    exact map_conj_eq_one _ _ _ _ hbb (map_evAt_eq_one D hF A v κ hA hv)
  intro i j
  have h3 := congrFun (congrFun hF1 i) j
  change evAt D v (finPart D ((Formalism.L2.Theta.mt V (P.ψ κ) - 1) i j)) = 0
  rw [Matrix.sub_apply, RingHom.map_sub, RingHom.map_sub]
  change evAt D v (finMat D.sp.cm.sig V.gram (P.ψ κ) i j) - _ = 0
  rw [Matrix.map_apply] at h3
  rw [h3, sub_eq_zero]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

end GlobalTheory.FrameOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRingStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriedFrames_specialise_flagComponent_localRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk := by
  first | exact @GlobalTheory.CarrySpec.carries_spec | exact GlobalTheory.CarrySpec.carries_spec | (intros; apply GlobalTheory.CarrySpec.carries_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellMultiplicityPositiveConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_multiplicity_positive_cone : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    0 < c j → (∀ i, i ∈ Set.range e ↔ i ≠ j) → 0 < cellMult bar δ →
    (cellMult bar (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) : ℝ) = c j * cellMult bar δ := by
  first | exact @GlobalTheory.PolFan.ConsMult.cellMult_cons_eq | exact GlobalTheory.PolFan.ConsMult.cellMult_cons_eq | (intros; apply GlobalTheory.PolFan.ConsMult.cellMult_cons_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesMembershipTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TwTameCell

theorem tameAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (h : χ.TameAt v) (h' : χ'.TameAt v) : (χ * χ').TameAt v := fun y hy hy1 => by
  rw [HChar.loc_mul, h y hy hy1, h' y hy hy1, mul_one]

theorem tameAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).TameAt v :=
  fun _ _ _ => rfl

theorem eta_tameAt : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → (eta (D := Dof x) (cfOf x) w.I.xi v j).TameAt P' := by
  intro _ hL
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j _ _ _ P' _
  have h1 := ((cfOf x).isMu0 j).tame P'
  have hx : w.I.xi ((Dof x).what₂.muTw v) ∈ T.set f := w.xi_range ▸ Set.mem_range_self _
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hx
  have h2 : (w.I.xi ((Dof x).what₂.muTw v)).TameAt P' := by
    rcases hx with (h | h | h) | ⟨w', h⟩
    · rw [h]; exact tameAt_one P'
    · rw [h]; exact f.isDel.tame P'
    · rw [h]; exact f.isDel'.tame P'
    · rw [← h]
      unfold TwDat.xiTw
      split_ifs
      · exact tameAt_mul (f.isDel'.tame P') ((T.psi_is w').tame P')
      · exact tameAt_mul (f.isDel.tame P') ((T.psi_is w').tame P')
  exact tameAt_mul h1 h2

end GlobalTheory.TwTameCell

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesOfAdmissibleTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.SepPlaces

theorem mem_of_conj {R : Ranks} (H : Host R) (p : ℕ) {w w' : HeightOneSpectrum (𝓞 H.E)}
    (h : IsConjPl H w w') : w ∈ placesOver H.E p ↔ w' ∈ placesOver H.E p := by
  have hc : ((p : 𝓞 H.E) : H.E) = H.conj ((p : 𝓞 H.E) : H.E) := by
    push_cast; exact (map_natCast _ p).symm
  exact h _ _ hc

theorem not_mem_two {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {w : HeightOneSpectrum (𝓞 E)} (h1 : w ∈ placesOver E p) (h2 : w ∈ placesOver E q) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨a, b, hab⟩ := hc
  have h1' : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal := h2
  have : (1 : 𝓞 E) ∈ w.asIdeal := by
    have e : (1 : 𝓞 E) = (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (q : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1') (w.asIdeal.mul_mem_left _ h2')
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

theorem same_v (D : D7) (s s' : SplitPlace D.host.E) (h : s.v = s'.v) :
    s.w = s'.w ∨ IsConjPl D.host s'.w s.w := by
  apply GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s s'.w
  show Ideal.comap _ _ = _
  rw [s'.w_under, h]

end GlobalTheory.SepPlaces

namespace GlobalTheory.SepPlaces

theorem sep_gen (D : D7) {i : D.ntw.Tw} {j : ℕ} {b : Bool} {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} {e : ℤ} {W₀ : Type} [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] {ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀}
    {τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ}
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ)
    (hQ : ∀ P ∈ Q, P ∉ D.ntw.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k'))
    (P' : PlE D.host) (hP' : P' ∈ M.QP ∨ P' ∈ M.DP) :
    ¬ (P' ∈ M.QP ∧ P' ∈ M.DP) ∧ (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P').v) ∧
      (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P').v → P'' = P') ∧
      (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P').v → P'' = P') := by
  set pX := if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde with hpX
  have hpD : ∀ P, P ∈ D.ntw.pD i ↔ P ∈ placesOver D.host.E pX := fun P => by
    rw [← Finset.mem_coe, D.ntw.pD_eq i]
  have hpXp : pX.Prime := by
    rw [hpX]; split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hpXg : ∀ kk, pX ≠ D.host.g kk := fun kk => by
    rw [hpX]; split_ifs
    · exact (D.host.pde_ne_g kk).2
    · exact (D.host.pde_ne_g kk).1

  have hnotG : ∀ P, (P ∈ M.QP ∨ P ∈ M.DP) → ∀ kk, P ∉ placesOver D.host.E (D.host.g kk) := by
    rintro P (hP | hP) kk hg
    · exact (hQ P (M.QP_sub hP)).2 kk hg
    · exact not_mem_two hpXp (D.host.g_prime kk) (hpXg kk) ((hpD P).1 (M.DP_sub hP)) hg
  have hwP' : (M.sp P').w = P' := M.sp_w P' (by rcases hP' with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    exact (hQ P' (M.QP_sub h1)).1 (M.DP_sub h2)
  · intro kv hv
    have hwG : (M.sp (NX.pG D kv)).w = NX.pG D kv := M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))
    have hG : NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1) := D.naut.plGw_over kv.1 kv.2
    rcases same_v D _ _ hv with h | h
    · rw [hwG, hwP'] at h
      exact hnotG P' hP' kv.1 (h ▸ hG)
    · rw [hwG, hwP'] at h
      exact hnotG P' hP' kv.1 ((mem_of_conj D.host _ h).2 hG)
  · intro P'' hP'' hv
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inl hP'')
    rcases same_v D _ _ hv with h | h
    · rw [hw'', hwP'] at h; exact h
    · rw [hw'', hwP'] at h
      exfalso
      rcases hP' with h1 | h1
      · exact M.QP_nconj P' h1 P'' hP'' h
      · exact (hQ P'' (M.QP_sub hP'')).1
          ((hpD P'').2 ((mem_of_conj D.host _ h).1 ((hpD P').1 (M.DP_sub h1))))
  · intro P'' hP'' hv
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inr (Or.inl hP''))
    rcases same_v D _ _ hv with h | h
    · rw [hw'', hwP'] at h; exact h
    · rw [hw'', hwP'] at h
      exfalso
      rcases hP' with h1 | h1
      · exact (hQ P' (M.QP_sub h1)).1
          ((hpD P').2 ((mem_of_conj D.host _ h).2 ((hpD P'').1 (M.DP_sub hP''))))
      · exact M.DP_nconj P' h1 P'' hP'' h

end GlobalTheory.SepPlaces

namespace GlobalTheory.SepPlaces

theorem cell_places_sep : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → ¬ (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∧ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ (∀ kv, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') := by
  intro _ hL
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l v i b ψ hA j _ _ _ P' hP'
  exact sep_gen (Dof x) (cell (D := Dof x) l.b.Bs.exp b hA j) (fun P hP => hA.2.1 P hP) P' hP'

end GlobalTheory.SepPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellQPlacesOfAdmissibleTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.TameUnitOne

open Formalism.L2.NX

theorem tameVal_eq_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type}
    [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ)
    (hopen : IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal)
    (hI : ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A P → ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1)
    (u : 𝓞 E) (hu1 : u - 1 ∈ P.asIdeal) : NX.tameVal φ P e u = 1 := by
  have hu : u ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := P.asIdeal.sub_mem h hu1
    simpa using this))
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω P
  obtain ⟨hq2, -⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  have hϖne : algebraMap E Ω (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have h' : ((ϖ : E)) = 0 := (map_eq_zero _).1 h
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h']
    exact zero_mem _
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) (show 0 < Formalism.ConjugateSelfDual.normV P - 1 by omega)
  have hπne : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hϖne hπ.symm
  have hv : A.valuation ((1 : Formalism.ConjugateSelfDual.G E Ω) π / π - algebraMap E Ω (u : E)) < 1 := by
    rw [AlgEquiv.one_apply, div_self hπne]
    have h1 := (hA (u - 1)).2 hu1
    have e1 : (1 : Ω) - algebraMap E Ω (u : E) = -(algebraMap E Ω (((u - 1 : 𝓞 E)) : E)) := by
      push_cast
      ring
    rw [e1, Valuation.map_neg]
    exact h1
  have hT := GlobalTheory.TameResRead.tameRep_zpow hA (one_mem _) hϖ1 hϖ2 hπ hu hv e
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep φ P e m hopen hm hI _ u hu hT, one_zpow, map_one]

end GlobalTheory.TameUnitOne

namespace GlobalTheory.LevCmp

theorem tameVal_wild_one : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' l.b.Bs.exp.sgnT u = 1) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ((Dof x).ntw.delta i) P'' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) u = 1) := by
  intro _ hL
  refine StepW.of_all fun _ B _ T _ _ _ _ P x l v i b ψ hA j _ _ _ => ?_
  refine ⟨fun P'' hP'' u hu => ?_, fun P'' hP'' u hu => ?_⟩
  · have hQ : P'' ∈ QOf P v := (cell (D := Dof x) l.b.Bs.exp b hA j).QP_sub hP''
    exact GlobalTheory.TameUnitOne.tameVal_eq_one ψ P'' _ ((Dof x).ntw.l i) hA.2.2.1 (hA.1 P'' hQ).2
      (fun _ _ σ _ => hA.2.2.2.2.1 σ) u hu
  · have hD : P'' ∈ (Dof x).ntw.pD i := (cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP''
    refine GlobalTheory.TameUnitOne.tameVal_eq_one ((Dof x).ntw.delta i) P'' _ 15 ((Dof x).ntw.delta_open i) ?_
      (fun A hA' σ hσ => ⟨1, ?_⟩) u hu
    · intro h
      have h1 := (Dof x).ntw.delta_tame i P'' hD
      have h2 : Ideal.absNorm P''.asIdeal ∣ 15 ^ Module.finrank ℤ (𝓞 (Dof x).host.E) := by
        have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
        rwa [Ideal.absNorm_span_natCast] at this
      have h3 : Nat.Coprime (Ideal.absNorm P''.asIdeal) 15 := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1]
        rfl
      have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ h3) h2
      exact P''.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h4)
    · have h1 := pow_card_eq_one' (x := (⟨(Dof x).ntw.delta i σ, σ, hσ, rfl⟩ :
        (ReciprocityTheory.Gal.Ine (F := (Dof x).host.E) A).map ((Dof x).ntw.delta i)))
      rw [(Dof x).ntw.delta_15 i P'' hD A hA'] at h1
      rw [pow_one]
      exact congrArg Subtype.val h1

end GlobalTheory.LevCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellRayInConeOfMarkedFormPieces
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan.OrbMark

theorem exists_face_coord_of_linearOn {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m k : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar φ γ)
    (hind : LinearIndependent ℤ γ) {e : Fin k → LinearMap.BilinForm ℤ X} (hem : ∀ i, e i ∈ balForms bar X)
    (hen : ∀ i y, 0 ≤ e i y y) (hel : φ.LinearOn e) {v : LinearMap.BilinForm ℤ X} {t : Fin m → ℝ} {b : Fin k → ℝ}
    (ht : ∀ i, 0 ≤ t i) (hb : ∀ i, 0 < b i) (hvt : toReal v = ∑ i, t i • toReal (γ i))
    (hvb : toReal v = ∑ i, b i • toReal (e i)) (j : Fin k) :
    ∃ a : Fin m → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧ toReal (e j) = ∑ i, a i • toReal (γ i) := by
  have h := GlobalTheory.T.inRealCone_cell_of_linearPiece_through_cellPoint bar φ γ e hγ hem hen hel v t b ht hb hvt hvb
  choose a ha he using h
  have h1 : toReal v = ∑ i, (∑ l, b l * a l i) • toReal (γ i) := by
    rw [hvb]
    simp only [he, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 : (fun i => (∑ l, b l * a l i) - t i) = 0 := by
    refine eq_zero_of_toReal_rel (u := γ) (v := (![] : Fin 0 → _)) (s := ![]) (fun d c hc => ?_) ?_
    · funext i
      exact Fintype.linearIndependent_iff.1 hind c (by simpa using hc) i
    · simp only [sub_smul, Finset.sum_sub_distrib, ← h1, ← hvt]
      simp
  refine ⟨a j, ha j, fun i hi => ?_, he j⟩
  have h3 : ∑ l, b l * a l i = 0 := by
    have := congrFun h2 i
    simpa [hi] using this
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => mul_nonneg (hb l).le (ha l i)).1 h3 j (Finset.mem_univ _)
  exact (mul_eq_zero.1 h4).resolve_left (hb j).ne'

theorem mem_balForms_of_descend {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X Y : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] (τ : 𝓞 E ≃+* 𝓞 E) {f : X →+ Y} (hf : Function.Surjective f)
    (hsm : ∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) {δ : LinearMap.BilinForm ℤ X} (hδ : δ ∈ balForms H.bar X)
    {ε : LinearMap.BilinForm ℤ Y} (hε : ∀ x y, ε (f x) (f y) = δ x y) : ε ∈ balForms H.bar Y := by
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z
    rw [hε, hε, hδ.1]
  · obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z
    obtain ⟨a, rfl⟩ := τ.surjective a
    rw [← GlobalTheory.T.ringOfIntegers_aut_comm_hostConjugation E H τ a, ← hsm, ← hsm, hε, hε, hδ.2]

theorem exists_coord_pullAdd_of_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell H.bar φ δ₀ → LinearIndependent ℤ δ₀ →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] (π : X₀ →ₗ[𝓞 E] Y), Function.Surjective π → ∀ (τ : 𝓞 E ≃+* 𝓞 E) (f : X →+ Y), τ H.w0 = H.w0 →
    Function.Surjective f → (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y, (∀ i, 0 < t i → pull π (u i) = δ₀ i) →
  ∀ β : LinearMap.BilinForm ℤ X, (∀ (x y : X) (x₀ y₀ : X₀), π x₀ = f x → π y₀ = f y → β x y = v x₀ y₀) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
    toReal (δ j) = ∑ i, a i • toReal (pullAdd f (u i)) := by
  intro E _ _ _ H φ htw X₀ _ _ _ m₀ δ₀ h₀ hind v t ht hvt X Y _ _ _ _ _ _ π hπ τ f hτ hf hsm u hu β hβ m δ hδ c hc hβc j hj
  classical
  have hval : ∀ x y, (β x y : ℝ) = ∑ l, c l * (δ l x y : ℝ) := fun x y => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hβc x y
  have hvan : ∀ l, 0 < c l → ∀ x, f x = 0 → ∀ y, δ l x y = 0 := by
    intro l hl x hx y
    have hb : β x x = 0 := by simpa using hβ x x 0 0 (by simp [hx]) (by simp [hx])
    have hk := hval x x
    rw [hb, Int.cast_zero] at hk
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hc i) (Int.cast_nonneg (hδ.nonneg i x))).1 hk.symm l (Finset.mem_univ _)
    have h0 : δ l x x = 0 := Int.cast_eq_zero.1 ((mul_eq_zero.1 hall).resolve_left hl.ne')
    exact ConeSub.eq_zero_of_self_eq_zero (δ l) (hδ.mem l).1 (hδ.nonneg l) h0 y
  set S : Finset (Fin m) := Finset.univ.filter fun l => 0 < c l with hS
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Set.range s = ↑S := Finset.range_orderEmbOfFin S rfl
  have hspos : ∀ i, 0 < c (s i) := fun i => by
    have : s i ∈ (S : Set (Fin m)) := hs ▸ Set.mem_range_self i
    simpa [hS] using this
  have hdesc : ∀ i : Fin S.card, ∃ ε : LinearMap.BilinForm ℤ Y, ∀ x y, ε (f x) (f y) = δ (s i) x y := fun i =>
    GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf _ (hvan _ (hspos i)) fun x hx y => by rw [(hδ.mem _).1]; exact hvan _ (hspos i) x hx y
  choose ε hε using hdesc
  have hεm : ∀ i, ε i ∈ balForms H.bar Y := fun i => mem_balForms_of_descend H τ hf hsm (hδ.mem _) (hε i)
  have hεn : ∀ i y, 0 ≤ ε i y y := fun i y => by
    obtain ⟨y, rfl⟩ := hf y
    rw [hε]; exact hδ.nonneg _ _
  have hsemi := eval_pull_semilinear_of_isTwInv E H φ htw τ hτ f hf hsm
  have hεl : φ.LinearOn ε := by
    intro d hd
    have h1 := linearOn_comp hδ.linear s d hd
    have h2 : ∀ i, φ.evalZ (δ (s i)) = φ.evalZ (ε i) := fun i => by
      have := hsemi fun a b => (ε i a b : ℝ)
      simp only [hε] at this
      exact this
    have h3 := hsemi fun a b => ∑ i, d i * (ε i a b : ℝ)
    simp only [hε] at h3
    simp only [h2] at h1
    exact h3.symm.trans h1
  have hvb : toReal v = ∑ i, c (s i) • toReal (pull π (ε i)) := LinearMap.ext₂ fun x₀ y₀ => by
    obtain ⟨x, hx⟩ := hf (π x₀)
    obtain ⟨y, hy⟩ := hf (π y₀)
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pull_apply]
    rw [← hβ x y x₀ y₀ hx.symm hy.symm, hval, ← hx, ← hy]
    simp only [hε]
    refine (Fintype.sum_of_injective s s.injective _ _ (fun l hl => ?_) fun i => rfl).symm
    have : ¬ 0 < c l := by rw [hs] at hl; simpa [hS] using hl
    rw [le_antisymm (not_lt.1 this) (hc l), zero_mul]
  obtain ⟨j, rfl⟩ : j ∈ Set.range s := by rw [hs]; simpa [hS] using hj
  obtain ⟨a, ha, ha0, he⟩ := exists_face_coord_of_linearOn h₀ hind (fun i => pull_mem π (hεm i)) (fun i y => hεn i _)
    ((linearOn_pull_iff hπ).2 hεl) ht hspos hvt hvb j
  refine ⟨a, ha, ha0, LinearMap.ext₂ fun x y => ?_⟩
  obtain ⟨x₀, hx⟩ := hπ (f x)
  obtain ⟨y₀, hy⟩ := hπ (f y)
  have h1 := LinearMap.congr_fun₂ he x₀ y₀
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pull_apply, pullAdd_apply] at h1 ⊢
  rw [hx, hy, hε] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (ht i).eq_or_lt with h | h
  · rw [ha0 i h.symm, zero_mul, zero_mul]
  · rw [← hu i h, pull_apply, hx, hy]

end GlobalTheory.PolFan.OrbMark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralCharacterIntegralStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_integral : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.PendOf.CenInt (w.D Z) := by
  first | exact @GlobalTheory.CenIntAtLoc.cenInt_at | exact GlobalTheory.CenIntAtLoc.cenInt_at | (intros; apply GlobalTheory.CenIntAtLoc.cenInt_at <;> assumption)
end

