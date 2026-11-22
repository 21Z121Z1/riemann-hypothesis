import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.Bundle0035
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftMarked
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.Bundle0032
import Formalism.LocalToGlobal.Columns.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0405
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0435
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdelicUnitaryConjIntegralFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

set_option maxHeartbeats 1000000

namespace GlobalTheory.Mem.R3.LiftBrg.FrameEquiv

theorem castGL_castGL_symm {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (x : GL (Fin n) R) :
    castGL h (castGL h.symm x) = x := by
  subst h
  ext i j
  simp [castGL]

theorem bc_swapAE_injective (D : D7) (m : ℕ) :
    Function.Injective (Formalism.UG.bc (n := Fin m) (swapAE D)) := by
  intro a b h
  have hs : Function.Injective (swapAE D) := fun x y hxy =>
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective hxy
  ext i j
  have := congrArg (fun g : GL (Fin m) (Formalism.IndefR.Lev.EAf D) => g.val i j) h
  exact hs this

theorem frame_equiv : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k),
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
  intro X px I hX U Xg tr L i t A k hF
  obtain ⟨-, -, h3, hk, -, -⟩ := hF
  set V := Vc X.toD7 i
  set h := rkEq X i
  set G := Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV
  let c : Bridge.Gf V →* GL (Fin X.B.R.nV) (EA X) :=
    (castGL h.symm).toMonoidHom.comp ((Formalism.UG.bc (swapAE X.toD7)).comp (Bridge.Gf V).subtype)
  have hc : ∀ g, c g = castGL h.symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _)) := fun _ => rfl
  have hmem : ∀ g : Bridge.Gf V, (A * k)⁻¹ * c g * (A * k) ∈ G := by
    intro g
    have hUA : Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _) ∈ UA X.toD7.sp.cm V.gram := by
      obtain ⟨κ, hκ⟩ := g.2
      rw [← hκ]
      exact GlobalTheory.LevFinCong.finE_mem_UA V κ
    have hx : A⁻¹ * c g * A ∈ G := by
      rw [h3]
      have e : A * (A⁻¹ * c g * A) * A⁻¹ = c g := by group
      rw [e, hc, castGL_castGL_symm]
      exact hUA
    have e2 : (A * k)⁻¹ * c g * (A * k) = k⁻¹ * (A⁻¹ * c g * A) * k := by group
    rw [e2]
    exact G.mul_mem (G.mul_mem (G.inv_mem hk) hx) hk
  let ψ : Bridge.Gf V →* G :=
    { toFun := fun g => ⟨(A * k)⁻¹ * c g * (A * k), hmem g⟩
      map_one' := by ext1; simp
      map_mul' := fun a b => by ext1; simp only [map_mul, Subgroup.coe_mul]; group }
  have hψ : ∀ g, ((ψ g : G) : GL (Fin X.B.R.nV) (EA X)) = (A * k)⁻¹ * c g * (A * k) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    intro a b hab
    have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) hab
    simp only [hψ, mul_left_inj, mul_right_inj] at e
    rw [hc, hc] at e
    have e' := (castGL h.symm).injective e
    exact Subtype.ext (bc_swapAE_injective X.toD7 V.rank e')
  have hsurj : Function.Surjective ψ := by
    intro u
    have hku : k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hk u.2) (G.inv_mem hk)
    have hw := (h3 _).1 hku
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.AdIsomCorrection.exists_finE V _ hw
    refine ⟨⟨finHom V κ, κ, rfl⟩, ?_⟩
    ext1
    rw [hψ, hc]
    change (A * k)⁻¹ * castGL h.symm (finE V κ) * (A * k) = _
    rw [hκ, castGL_castGL_symm h.symm]
    group
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  let Ψ := MulEquiv.ofBijective ψ hbij
  refine ⟨Ψ.symm, fun u => ?_⟩
  have e0 : ψ (Ψ.symm u) = u := Ψ.apply_symm_apply u
  have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) e0
  simp only [hψ] at e
  rw [← hc, ← e]
  group

end GlobalTheory.Mem.R3.LiftBrg.FrameEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

theorem mem_HHa_of_span {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : P ∈ Submodule.span k (HHa r n k cc isX a)) : P ∈ HHa r n k cc isX a := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, fun σ i i' hi t => by rw [map_add, hx.2.1 σ i i' hi t, hy.2.1 σ i i' hi t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx.2.2 m h
    · exact hy.2.2 m h
  | smul c x _ hx =>
    exact ⟨Submodule.smul_mem _ c hx.1, fun σ i i' hi t => by rw [map_smul, hx.2.1 σ i i' hi t],
      fun m hm => hx.2.2 m (MvPolynomial.support_smul hm)⟩

theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : RowDeg r n k a P) : P.IsHomogeneous (∑ σ, ∑ j : Fin (r σ), a σ j) := by
  intro m hm
  have h1 := h m (MvPolynomial.mem_support_iff.2 hm)
  rw [show Finsupp.weight 1 m = Finsupp.degree m from (DFunLike.congr_fun Finsupp.degree_eq_weight_one m).symm,
    Finsupp.degree_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => h1 σ j

theorem exists_isVarOf {D : D7} (V W : HSp D) {r : ℕ} (hr : W.rank = r) (X : Data D.host.E r) (hX : IsMod W hr X) (q0 : ℕ)
    (hq : X.p0 + q0 = r) : ∃ vr, IsVarOf V W X q0 vr := by
  let e1 : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hX.psi _).2 ⟨ρ, rfl⟩⟩)
    ⟨fun a b h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hX.psi τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  let e2 : Fin q0 ⊕ Fin X.p0 ≃ Fin W.rank := finSumFinEquiv.trans (finCongr (by omega))
  refine ⟨e1.symm.prodCongr (e2.prodCongr (Equiv.refl _)), fun l => ⟨?_, rfl, ?_⟩⟩
  · exact (congrArg Subtype.val (e1.apply_symm_apply l.1)).symm
  · obtain ⟨τ, j | j, b⟩ := l <;> rfl

theorem exists_isDetAt {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) (V : HSp D) (g : GA D V) :
    ∃ y, IsDetAt e V g y := by
  obtain ⟨ι, Q, es, h1, h2, h3⟩ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum h
  have he : e * e = e := by
    conv_lhs => rw [h3, Finset.sum_mul]
    rw [h3]
    exact Finset.sum_congr rfl fun i hi => GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hi
  obtain ⟨u, hu⟩ : IsUnit (Formalism.L2.Theta.mt V g).det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨(matHom V g), rfl⟩
  have k1 : (e * (u : AE D) + (1 - e)) * (e * (u⁻¹ : (AE D)ˣ) + (1 - e)) = 1 := by
    have := u.mul_inv
    linear_combination (e * e) * this + ((2 : AE D) - u - (u⁻¹ : (AE D)ˣ)) * he
  exact ⟨⟨_, _, k1, (mul_comm _ _).trans k1⟩, by rw [IsDetAt, ← hu]⟩

theorem exists_point {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (hA : l.A = 1)
    (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hmk : ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (h : GA D W), IsONFr (U.X (dict h).1) (dict h).2 ∧
      ∃ γ, AtComp θ W hr U.X dict x₀ h γ ∧ MarkAd l W hr ι (γ * h) (Wt.mark (dict h).1))
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (hD : Dom a V.rank) (mu : GA D W → ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cst : U.Comp → ℂ)
    (hcc : CcIs θ V W hr U dict mu x₀ om f₀ cst) (h : GA D W) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (Dc : Dic Dw c σ (U.X (dict h).1) g Dw.p V.rank a) (γ : GA D W)
      (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (v : TF V.rank g) (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ)
      (B : AnFib (U.X (dict h).1) Dc.bas Dc.idx Dc.e (dict h).2 (U.X (dict h).1).Λ
        (unC (Formalism.L2.PjFree.Unf.ofPj U) (dict h).1 ⟨(dict h).2, hx⟩)),
      AtComp θ W hr U.X dict x₀ h γ ∧ SelfD (U.X (dict h).1) (U.X (dict h).1).Λ ∧ IsMark l (U.X (dict h).1).Λ mk ∧
      B.Marked mk ∧ MarkAd l W hr ι (γ * h) mk ∧
      B.Reads 1 (unC (Formalism.L2.PjFree.Unf.ofPj U) (dict h).1 ⟨(dict h).2, hx⟩).s ϑ ∧
      IsVac (U.X (dict h).1) Dc.bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) (U.X (dict h).1).Λ) v ∧
      (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA (U.X (dict h).1) Dc.bas Dc.idx v (dict h).2 z) ∧
      Reads θ V W hr (U.X (dict h).1) Dc.bas Dc.idx (om (1, γ * h) f₀) ((cst (dict h).1 * mu h * κ') • v) (dict h).2 := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Wt⟩ := nonempty_uw (U := Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨hon, γ, hat, hma⟩ := hmk Wt h
  have hn : Even V.rank := hD.2
  obtain ⟨-, hsd, hmark, -⟩ := uw_lattice _ H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU h1 Wt (dict h).1
  obtain ⟨Dc, hDe, -⟩ := exists_dic _ H Dw l c σ r Wt.g V.rank (U.X (dict h).1) a Wt.e hσ hU.1 (hU.2.1 _).1 (hU.2.1 _).2 hsd hD
  obtain ⟨hx, hux, -⟩ := hx_of_isONFr _ r Wt.g V.rank _ Dc.bas Dc.idx Dc.sympl hn _ hon
  have hw : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hw' : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset V.rank 1)).1
  have key := uw_anFib _ H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU h1 Wt (dict h).1 Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx⟩ hux
  rw [← hDe] at key
  obtain ⟨B, hBm, ϑ, hϑ, -⟩ := key
  have hT := isTheta1_of_reads_generator _ H Dw l Xo c _ _ _ Dc.bas Dc.idx Dc.e _ _ _ B Dc.sympl hx hsd ϑ hϑ
  obtain ⟨κ', hκ⟩ := VacProd.prod_eq_mul_thA _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hn _ hw hw' _ hsd v hv _ hx ϑ hT
  refine ⟨hx, Wt.g, Dc, γ, Wt.mark (dict h).1, v, ϑ, κ', B, hat, hsd, hmark, hBm, hma, hϑ, hv, hκ, ?_⟩
  obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ r Wt.g V.rank _ Dc.bas Dc.idx Dc.sympl hn _ hx v hv.1).2.2 v hv.1).1
    (cst (dict h).1 * mu h * κ') 0
  rw [zero_smul, add_zero] at s1 s2
  rw [zero_smul, add_zero] at s2
  refine ⟨s1, fun w hw0 => ?_⟩
  rw [hcc.2 h γ hat hx Wt.g Dc.bas Dc.idx Dc.e Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ ϑ ⟨B, hϑ⟩ w hw0, hκ, s2, Pi.smul_apply, smul_eq_mul]
  ring

theorem dict_cast {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)
    (W : HSp D) (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) ∧
    LatIsom W (T.Q.Dw j).EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) ∧
    (∀ g : GA D W, ∃ x, IsDetRoot W g x) ∧
    ∀ θ : InfFam D, IsInfFam θ → (∀ k, IsMod W hr ((T.U j σ).X k)) → 1 ≤ D.R.r →
      ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))) (h : GA D W),
        IsONFr ((T.U j σ).X (castDict hV (T.dict j σ) h).1) (castDict hV (T.dict j σ) h).2 ∧
        ∃ γ, AtComp θ W hr (T.U j σ).X (castDict hV (T.dict j σ)) (T.x₀ j σ) h γ ∧
          MarkAd T.Q.l W hr (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (γ * h)
            (Wt.mark (castDict hV (T.dict j σ) h).1) := by
  subst hV
  obtain ⟨_, g, e, F, ik, φ, th, h1, h2, h3, h4⟩ := hL.adPin j hj σ hσ
  refine ⟨h1, h2, (hL.muVal j hj σ hσ).1, fun θ hθ hm h0 Wt h => ?_⟩
  obtain ⟨k1, γ, k2, k3, -⟩ := dict_atComp_markAd D _ _ _ _ _ σ _ (T.U j σ) hσ (hL.unf j hj σ hσ) h0 hL.pins.2.1.2 θ _ hr
    (T.dict j σ) _ g e F ik φ th _ hθ hm (hL.familyUniformisationBasePointOrthogonal j hj σ hσ) h3 h4 Wt h
  exact ⟨k1, γ, k2, k3⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

abbrev unfO (O : OMDat T.toCore R i Tp tup) : Unf (T.Q.Xo ((i : ℕ) + 1)) O.c' (inC O.c') D.R.r :=
  unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')

set_option maxHeartbeats 1000000 in

theorem geo_value (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {c0 : ℂ} (hc : CovAt O c0) (t : Tp)
    (X : Data D.host.E D.R.r) (g : ℕ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (k : GA D (Wc D i)) (xk : (AE D)ˣ) (hk : IsDetRoot (Wc D i) k xk) (hX : IsMod (Wc D i) (rank_Wc i) X)
    (hp : X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q) (hpq : (T.Q.Dw ((i : ℕ) + 1)).p ≠ (T.Q.Dw ((i : ℕ) + 1)).q)
    (hrk : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) (hn : Even (Vc D i).rank)
    (hΛ : latR (rank_Wc i) (latG (Wc D i) k) = X.Λ) (hsd : SelfD X X.Λ) (x : Frame X.Ψ D.R.r) (hx : x ∈ X.dom)
    (hxk : x = frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.x₀ ((i : ℕ) + 1) O.s0 τ.1))
    (mk mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (hm : IsMark T.Q.l X.Λ mk)
    (hm₂ : IsMark (O.dδ t).l₂ X.Λ mk₂) (ha₂ : MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) k mk₂)
    (hov : MarkOver T.Q.l (O.dδ t).l₂ X.Λ mk mk₂) (v : TF (Vc D i).rank g) (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ)
    (hv : IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) X.Λ) v)
    (hκ : ∀ z : Fin (Vc D i).rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X Dc.bas Dc.idx v x z)
    (Y : O.Cl' t → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E)
    (hY : ∀ j, IsRoots (O.dδ t).l₂ X.Λ mk₂ (O.Nc t j) (Y j)) (xs : O.Cl' t → VsV D i O.c'.F)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c') (hf : GlobalTheory.OneMapTuples.IsCls O t xs f) :
    letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
    ∀ (y : FrPt (T.Q.Xo ((i : ℕ) + 1)) O.c' ℂ) (B : AnFib X Dc.bas Dc.idx Dc.e x X.Λ y), B.Marked mk → B.Reads 1 y.s ϑ →
      evR (T.Q.Xo ((i : ℕ) + 1)) O.c' f y = c0 * ((R.xi (tup t) xk : Circle) : ℂ) * κ' *
        clsSum (inC O.c') X Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t)
          (fun j => O.io (xs j)) X.Λ v Y x := by
  letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
  letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra
  intro y B hB hϑ
  have halg : ∀ s : O.c'.F, algebraMap (O.dδ t).c₂.F ℂ ((O.dδ t).eF s) = algebraMap O.c'.F ℂ s := fun s => rfl
  obtain ⟨hlev, hA₂, hnab⟩ := hP.cov t
  obtain ⟨y₂, B₂, hov₂, hB₂, hrd⟩ := MarkLift.exists_lift_marked _ _ _ _ _ O.c' _ (O.dδ t) halg hlev hT.laws.pins.2.1.2 hA₂
    (fun h => absurd h hpq) _ g X Dc.bas Dc.idx Dc.e x X.Λ y B Dc.sympl hx hsd mk mk₂ hm hB hm₂ hov
  obtain ⟨-, cga, hio⟩ := hP.io
  have h1 := evR_eq_clsSum GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ t) halg hnab _ g X Dc.bas Dc.idx Dc.e x X.Λ y y₂ B₂ hov₂
    Dc.sympl hx hsd _ Dc.hr Dc.eL hrk hn Dc.dir_eq ϑ v κ' (hrd ϑ hϑ) hv hκ mk₂ hm₂ hB₂ (O.Cl' t) (O.w t) (O.La t) (O.Nc t)
    (O.gam t) (O.vol t) (O.ep t) _ O.io xs (wtA (κ i))
    (fun j => ⟨((hP.reps t).1 j).1, ((hP.reps t).1 j).2.2.1, ((hP.reps t).1 j).2.2.2.1⟩)
    (fun j => mem_HHa_of_span _ _ _ _ _ _ (hio.2.2.1 ▸ LinearMap.mem_range_self _ _)) Y hY f hf
  subst hxk
  rw [h1, hc t X g Dc.bas Dc.idx Dc.e k xk mk₂ hX hp Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ hΛ hk hm₂ ha₂ y₂ B₂ hB₂]
  rfl

end GlobalTheory.PtId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimesNotSelfConjugateDisjointTypeTwist
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
noncomputable section

namespace GlobalTheory.Mem.PrimesAtLevel

theorem not_both_mem {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hpP : (p : R) ∈ P) (hqP : (q : R) ∈ P) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  have h1 : ((a * p + b * q : ℤ) : R) = 1 := by rw [hab, Int.cast_one]
  push_cast at h1
  apply (inferInstance : P.IsPrime).ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hqP)

theorem primes_atT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (v : (I.atT l u a).vT), conjPrime₂ v.1 ≠ v.1 ∧ (∀ w ∈ (B.primes X).vGs, ¬ IsOver (v.1.under (𝓞 B.host.F)) w) ∧ (∀ P ∈ I.Q a, ¬ IsOver (v.1.under (𝓞 B.host.F)) P) ∧ Disjoint (B.primes X).vGs (I.Q a) := by
  intro B X I hI l u a v
  obtain ⟨P, hP⟩ := v
  dsimp only at hP ⊢
  have hpr := l.pr
  have hpiT : (B.primes X).piT u ∈ P.asIdeal := by
    unfold Primes.vT divs at hP
    split_ifs at hP with h
    · exact h.mem_toFinset.mp hP
    · simp at hP
  have hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hpr.piT_norm u]
    exact P.asIdeal.mul_mem_right _ hpiT
  have hTF : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal := by
    show _ ∈ Ideal.comap (algebraMap _ _) _
    rw [Ideal.mem_comap, map_natCast]
    exact hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc
    have h2 : B.fields.conjO ((B.primes X).piT u) ∈ P.asIdeal := by
      have h3 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := by rw [hc]; exact hpiT
      exact (mem_conjP P _).mp h3
    obtain ⟨x, y, hxy⟩ := hpr.piT_cop u
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hxy]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpiT) (P.asIdeal.mul_mem_left _ h2)
  · intro w hw hov
    have hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      rw [IsOver] at hov
      rw [hov, Ideal.mem_comap, map_natCast] at hTF
      exact hTF
    obtain ⟨i, hi⟩ : ∃ i, w ∈ (B.primes X).vG i := by
      classical
      rcases Finset.mem_union.mp hw with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hgw : (((B.primes X).g i : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have hc : B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal := by
        unfold Primes.vG divs at hi
        split_ifs at hi with h
        · exact h.mem_toFinset.mp hi
        · simp at hi
      rw [← hpr.piG_norm i]
      exact w.asIdeal.mul_mem_left _ hc
    exact not_both_mem w.asIdeal (hpr.T_prime u) (hpr.g_prime i) (hpr.T_ne_g u i) hTw hgw
  · intro Q hQ hov
    obtain ⟨v, -, hsel, hgood⟩ := I.exists_of_mem_Q hQ
    have hv : v.asIdeal = (P.under (𝓞 B.host.F)).asIdeal := by
      rw [hov, ← hsel]
      exact (hI.sel_ok v).symm
    have hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem, hv]
      exact hTF
    have hd : ringChar (𝓞 B.fields.F ⧸ v.asIdeal) ∣ (B.primes X).T u := (ringChar.spec _ _).mp hTv
    rcases (Nat.dvd_prime (hpr.T_prime u)).mp hd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · apply hgood.2.2
      convert hI.T_mem u using 1
      exact h1
  · exact Finset.disjoint_right.mpr (Q_notMem_of_ok hI a)

end GlobalTheory.Mem.PrimesAtLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

set_option maxHeartbeats 1000000 in

theorem evalOn_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ EvalOn R X h t v₀ c (MultR R F) (conjRows X) := by
  intro hDS hCusp hU hFin D G' _ _ Pl0 T A Ks _ _ _ R F X h t hE hGap hl hi hν hsee
  obtain ⟨cc, hcc, hsm⟩ := GlobalTheory.T.contragredientModel_conjDiscreteSeries_of_gap hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  let v₀ : (MP R).Vec := fun τ => ⟨(cc τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, cc τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(cc τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  obtain ⟨c0, hc0, hN⟩ := GlobalTheory.T.translatedEvaluation_squareIntegrable_norm_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  have hI := GlobalTheory.T.conj_translated_level_row_evaluation_mem_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  have hO := GlobalTheory.T.exists_rowLevel_translatedEvaluation_of_conj_row hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  refine ⟨v₀, hnorm, c0, hc0, ?_⟩
  classical
  have hmem : ∀ S : MultR R F, MemLp (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) 2 (muX X) :=
    fun S => (hN v₀ hnorm S S.2).1
  let Φ : MultR R F → conjRows X := fun S =>
    ⟨(hmem S).toLp _, hI S S.2 _ (hmem S).coeFn_toLp⟩
  have hΦ : ∀ S, ((Φ S : conjRows X) : L2X X) =ᵐ[muX X]
      (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) := fun S => (hmem S).coeFn_toLp
  have key : ∀ (S : MultR R F) (Fx : conjRows X), ((Fx : L2X X) =ᵐ[muX X]
      fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) → Φ S = Fx := by
    intro S Fx hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ S).trans hF.symm
  let L : MultR R F →ₗ[ℂ] conjRows X :=
    { toFun := Φ
      map_add' := fun S S' => by
        apply key
        have h1 := hΦ S
        have h2 := hΦ S'
        have h3 := Lp.coeFn_add ((Φ S : conjRows X) : L2X X) ((Φ S' : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a S => by
        rw [RingHom.id_apply]
        apply key
        have h1 := hΦ S
        have h3 := Lp.coeFn_smul a ((Φ S : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hLn : ∀ S : MultR R F, ‖((L S : conjRows X) : L2X X)‖ ^ 2 =
      c0 * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re := by
    intro S
    show ‖((hmem S).toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp (hmem S)]
    exact (hN v₀ hnorm S S.2).2.1
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro S hS
    have h1 := hLn S
    rw [hS] at h1
    simp only [ZeroMemClass.coe_zero, norm_zero] at h1
    have h2 : (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re = 0 := by
      rcases mul_eq_zero.mp (by rw [← h1]; ring : c0 * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re = 0) with h' | h'
      · exact absurd h' hc0.ne'
      · exact h'
    exact Subtype.ext ((hN v₀ hnorm S S.2).2.2 h2)
  have hsurj : Function.Surjective L := by
    intro Fx
    obtain ⟨S, hS, hF⟩ := hO (Fx : L2X X) Fx.2
    exact ⟨⟨S, hS⟩, key ⟨S, hS⟩ Fx hF⟩
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun S => ⟨hΦ S, hLn S⟩⟩

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugateStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeOver_splitPlace_eq_chosen_or_conjugate : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w := by
  first | exact @GlobalTheory.PlaceOverSplit.eq_or_eq_cP | exact GlobalTheory.PlaceOverSplit.eq_or_eq_cP | (intros; apply GlobalTheory.PlaceOverSplit.eq_or_eq_cP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftDefiniteSmoothModerateGrowthAnnihilatedStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_definite_smooth_moderate_growth_annihilated : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn T θ (lift om ν 𝓕 fun h => L (F h)) ∧ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsUnifModGrowth T θ (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ τ (Z : Mt T.rank), (∀ x h, RderC θ T τ Z (fun g => thetaKO om h g (L x)) = 0) → RderC θ T τ Z (lift om ν 𝓕 fun h => L (F h)) = 0 := by
  first | exact @GlobalTheory.DefLiftSmooth.lift_smooth_growth_killed | exact GlobalTheory.DefLiftSmooth.lift_smooth_growth_killed | (intros; apply GlobalTheory.DefLiftSmooth.lift_smooth_growth_killed <;> assumption)
end

