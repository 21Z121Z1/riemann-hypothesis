import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0091
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0043
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockRetr
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0090
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewHoldsGen
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem level_congr_mod_sq (D : D7) (u u' : D.what₂.Word) :
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD Formalism.MainNotions.S.Lat.gS D ^ 2] := by
  have h : Formalism.MainNotions.S.Lat.gS D ^ 2 ∣ D.modT := by unfold Formalism.MainNotions.S.Lat.gS; exact D.gg_dvd_modT
  exact (D.T_modEq_of_dvd u h).trans (D.T_modEq_of_dvd u' h).symm

theorem prodConvNew_holds {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) :
    ProdConvNew T.X u u' T.ψ := by
  have hg : ∀ v, TypAt T.X v → 0 < gAt T.X v := fun v hv =>
    (Formalism.L2.SG.Pf.typFacts_holds T.X T.hb u u' ⟨v, hv⟩).1.pos
  have hUZ := Formalism.L2.SG.Pf.LocalPositivity.localVolumeUnit_pos_and_ZZX_pos T.X u u' T.ψ T.ψ_char T.ψ_std (level_congr_mod_sq D u u') hg
  refine prodConvNew_ties T u u' fun v => ⟨fun _ => (hUZ v).1, (hUZ v).2, fun l => ?_,
    Formalism.L2.SG.Pf.LocalPositivity.jac_pos T.X hg v⟩
  by_cases hv : TypAt T.X v
  · exact pp_pos_typ T u u' v hv l
  · exact Formalism.L2.SG.Pf.LocalPositivity.pp_pos_ord T.X u u' T.ψ T.ψ_char T.ψ_std hv l

theorem prodConvNew_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConvNew X u u' ψ := by
  have hg : ∀ v, TypAt X v → 0 < gAt X v := fun v hv =>
    (Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩).1.pos
  have hUZ := Formalism.L2.SG.Pf.LocalPositivity.localVolumeUnit_pos_and_ZZX_pos X u u' ψ hψ hs (level_congr_mod_sq D u u') hg
  refine prodConvNew_gen X u u' ψ hb hψ hs hloc fun v => ⟨fun _ => (hUZ v).1, (hUZ v).2, fun l => ?_,
    Formalism.L2.SG.Pf.LocalPositivity.jac_pos X hg v⟩
  by_cases hv : TypAt X v
  · exact pp_pos_typ_gen X hb ψ hψ hs u u' v hv l
  · exact Formalism.L2.SG.Pf.LocalPositivity.pp_pos_ord X u u' ψ hψ hs hv l

theorem prodConvNew_onTied :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.OnTied fun _ X _ _ u u' _ ψ => ProdConvNew X u u' ψ := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' _ hb X0 ψ hT
  exact prodConvNew_holds_gen X hb ψ hT.2.1 hT.2.2.1 hT.2.2.2.2.1 u u'

theorem ProdConvAllNew : ∀ (D : D7) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word), u ≠ u' →
    Formalism.MainNotions.S.Cnt.Stand D u u' → ProdConvNew T.X u u' T.ψ :=
  fun _ T u u' _ _ => prodConvNew_holds T u u'

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxModes
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ}

theorem smul_eq_of_cx (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cx e X = cx e Y) :
    e.symm (1, 0) • X = e.symm (1, 0) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cx, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe] at this
  ext
  · simp [this]
  · simp

theorem smul_eq_of_cy (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cy e X = cy e Y) :
    e.symm (0, 1) • X = e.symm (0, 1) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cy, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe] at this
  ext
  · simp
  · simp [this]

theorem cx_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cx e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cx, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

theorem cy_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cy e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cy, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

end Split

section Data

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp)

theorem mode_data {p : PlF D} (hA : Agree δ M p) :
    ∃ (ex ey : (D.s.atP p).Ep) (d di gg ggi : Fin (D.R.rS + 1) → (D.s.atP p).Ep),
      ex ∈ (D.s.atP p).O ∧ ey ∈ (D.s.atP p).O ∧ ex * ex = ex ∧ ey * ey = ey ∧ ex + ey = 1 ∧ ex * ey = 0 ∧
      (∀ i, d i * di i = 1) ∧ (∀ i, gg i * ggi i = 1) ∧
      ∀ a b : Formalism.L2.SG.PairVal.MatR D,
        ex • lOf δ M p a b = ex • (Matrix.diagonal d * a.map (D.s.atP p).ιE * Matrix.diagonal di) ∧
        ey • ρOf δ M p a b = ey • (Matrix.diagonal ggi * (a.map (D.s.atP p).ιE).transpose * Matrix.diagonal gg) := by
  obtain ⟨-, -, -, -, -, hsp⟩ := id hA
  cases hM : (M p).split with
  | none =>
    refine ⟨1, 0, fun i => (M p).L.cj (frFac δ p i), fun i => Ring.inverse ((M p).L.cj (frFac δ p i)),
      fun _ => 1, fun _ => 1, (D.s.atP p).O.one_mem, (D.s.atP p).O.zero_mem, mul_one 1, mul_zero 0, add_zero 1,
      mul_zero 1, fun i => Ring.mul_inverse_cancel _ ((frFac_unit δ M hA i).map _), fun _ => mul_one 1, fun a b => ⟨?_, ?_⟩⟩
    · simp only [lOf, hM, one_smul]
      exact lL_eq _ _ _ a
    · simp only [zero_smul]
  | some g =>
    rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      have hx := fun i => (split_units δ M hA g i).1
      have hy := fun i => (split_units δ M hA g i).2
      have hmemO : ∀ a b : (D.s.atP p).Fp, a ∈ 𝒪[(D.s.atP p).Fp] → b ∈ 𝒪[(D.s.atP p).Fp] →
          g.e.symm (a, b) ∈ (D.s.atP p).O := by
        intro a b ha hb
        rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1, AlgEquiv.apply_symm_apply]
        exact ⟨ha, hb⟩
      refine ⟨g.e.symm (1, 0), g.e.symm (0, 1),
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).2), fun i => algebraMap _ _ ((g.e (frFac δ p i)).2)⁻¹,
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).1), fun i => algebraMap _ _ ((g.e (frFac δ p i)).1)⁻¹,
        hmemO 1 0 (Subring.one_mem _) (Subring.zero_mem _), hmemO 0 1 (Subring.zero_mem _) (Subring.one_mem _),
        ?_, ?_, ?_, ?_, fun i => by rw [← map_mul, mul_inv_cancel₀ (hy i), map_one],
        fun i => by rw [← map_mul, mul_inv_cancel₀ (hx i), map_one], fun a b => ⟨?_, ?_⟩⟩
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · simp only [lOf, hM]
        apply smul_eq_of_cx
        rw [cx_lG, cx_mul, cx_mul, cx_diag, cx_diag]
        rfl
      · simp only [ρOf, hM]
        apply smul_eq_of_cy
        rw [cy_ρG, cy_mul, cy_mul, cy_diag, cy_diag]
        rfl

end Data

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauTau
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

def sgnU : GLp p :=
  ⟨Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p,
    Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p⟩

def tau : GG p →* GG p where
  toFun x := (x.1, MulOpposite.op (sgnU p * x.2.unop * sgnU p))
  map_one' := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      show sgnU p * (1 : GLp p) * sgnU p = 1
      rw [mul_one, hs]
  map_mul' x y := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      simp only [Prod.snd_mul, MulOpposite.unop_mul, MulOpposite.unop_op]
      calc sgnU p * (y.2.unop * x.2.unop) * sgnU p
          = sgnU p * y.2.unop * (sgnU p * sgnU p) * x.2.unop * sgnU p := by rw [hs]; group
        _ = _ := by group

theorem tau_tau (x : GG p) : tau p (tau p x) = x := by
  have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
  ext1
  · rfl
  · apply MulOpposite.unop_injective
    show sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = x.2.unop
    calc sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = (sgnU p * sgnU p) * x.2.unop * (sgnU p * sgnU p) := by
          group
      _ = _ := by rw [hs]; group

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupMUIndep
section
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem witt_tuple {ι : Type} [Fintype ι] (x y : ι → S.V) (hx : LinearIndependent E x) (hy : LinearIndependent E y)
    (hG : ∀ i j, S.hT (x i) (x j) = S.hT (y i) (y j)) :
    ∃ g : S.V ≃ₗ[E] S.V, g ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ ∀ i, g (x i) = y i := by
  set U := Submodule.span E (Set.range x) with hU
  let b : Basis ι E U := Basis.span hx
  have hb : ∀ i, (b i : S.V) = x i := fun i => by
    show ((Basis.span hx i : U) : S.V) = x i
    rw [Basis.span_apply]
  let f : U →ₗ[E] S.V := b.constr E y
  have hfu : ∀ u : U, f u = ∑ i, b.equivFun u i • y i := fun u => b.constr_apply_fintype E y u
  have hu : ∀ u : U, (u : S.V) = ∑ i, b.equivFun u i • x i := by
    intro u
    have := congrArg Subtype.val (b.sum_repr u)
    rw [← this, Submodule.coe_sum]
    simp only [Submodule.coe_smul, hb, Basis.equivFun_apply]
  have hexp : ∀ (z : ι → S.V) (c d : ι → E), S.hT (∑ i, c i • z i) (∑ j, d j • z j) =
      ∑ i, ∑ j, star (c i) * d j * S.hT (z i) (z j) := by
    intro z c d
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hiso : ∀ u v : U, S.hT (f u) (f v) = S.hT u v := by
    intro u v
    rw [hfu, hfu, hu u, hu v, hexp, hexp]
    simp only [hG]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu0
    rw [LinearMap.mem_ker, hfu] at hu0
    have hc := Fintype.linearIndependent_iff.1 hy _ hu0
    refine (Submodule.mem_bot E).2 (Subtype.ext ?_)
    rw [hu u]
    simp [hc]
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem E S.V S.hT (fun x y => (hT_swap x y).symm)
    (fun x hx => S.nondeg.1 x hx) U f hinj hiso
  refine ⟨g, hg, fun i => ?_⟩
  have := hgf (b i)
  rw [hb] at this
  rw [this]
  exact b.constr_basis E y i

def tupMU (F : FlagG S r T) (F1 : FlagG S r T') (M U : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Fin (r + 1) ⊕ Fin (r + 1) → S.V :=
  Sum.elim (fun a => ∑ c, M c a • F.fvec c) (fun b => ∑ c, U c b • F1.fvec c)

theorem gram_moved (F : FlagG S r T) (F1 F2 : FlagG S r T') (M U : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hM : IsUpUni M) (hU : IsUpUni U) (hZ : Zhat F F2 = Mᴴ * Zhat F F1 * U) :
    ∀ i j, S.hT (tupMU F F1 M U i) (tupMU F F1 M U j) =
      S.hT (Sum.elim F.fvec F2.fvec i) (Sum.elim F.fvec F2.fvec j) := by
  have hexp : ∀ (z w : Fin (r + 1) → S.V) (c d : Fin (r + 1) → E), S.hT (∑ i, c i • z i) (∑ j, d j • w j) =
      ∑ i, ∑ j, star (c i) * d j * S.hT (z i) (w j) := by
    intro z w c d
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hFF : ∀ (G : FlagG S r T) c d, S.hT (G.fvec c) (G.fvec d) =
      if c = Fin.last r ∧ d = Fin.last r then -T else 0 := fun G c d => by
    have := brS_fvec G d c
    simp only [brS] at this
    rw [this]
    by_cases h1 : c = Fin.last r <;> by_cases h2 : d = Fin.last r <;> simp [h1, h2]
  have hFF' : ∀ (G : FlagG S r T') c d, S.hT (G.fvec c) (G.fvec d) =
      if c = Fin.last r ∧ d = Fin.last r then -T' else 0 := fun G c d => by
    have := brS_fvec G d c
    simp only [brS] at this
    rw [this]
    by_cases h1 : c = Fin.last r <;> by_cases h2 : d = Fin.last r <;> simp [h1, h2]
  have hdiag : ∀ (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : IsUpUni A) (t : E) (a b : Fin (r + 1)),
      ∑ i, ∑ j, star (A i a) * A j b * (if i = Fin.last r ∧ j = Fin.last r then t else 0) =
        if a = Fin.last r ∧ b = Fin.last r then t else 0 := by
    intro A hA t a b
    simp only [mul_ite, mul_zero, ite_and]
    rw [Finset.sum_eq_single (Fin.last r), Finset.sum_eq_single (Fin.last r)]
    · simp only [if_true, upUni_last hA]
      by_cases h1 : a = Fin.last r <;> by_cases h2 : b = Fin.last r <;> simp [h1, h2]
    · intro j _ hj; simp [hj]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  have hcross : ∀ a b, S.hT (tupMU F F1 M U (Sum.inl a)) (tupMU F F1 M U (Sum.inr b)) = S.hT (F.fvec a) (F2.fvec b) := by
    intro a b
    simp only [tupMU, Sum.elim_inl, Sum.elim_inr]
    rw [hexp]
    have h2 : S.hT (F.fvec a) (F2.fvec b) = Zhat F F2 a b := rfl
    rw [h2, hZ, Matrix.mul_apply]
    simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Zhat, brS]
    ring
  intro i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [tupMU, Sum.elim_inl]
    rw [hexp]
    simp only [hFF]
    exact hdiag M hM (-T) a b
  · exact hcross a b
  · rw [hT_swap, hcross b a, ← hT_swap]
    rfl
  · simp only [tupMU, Sum.elim_inr]
    rw [hexp]
    simp only [hFF']
    exact hdiag U hU (-T') a b

theorem tupMU_indep (F : FlagG S r T) (F1 : FlagG S r T') (M U : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hM : IsUpUni M) (hU : IsUpUni U) (hG : Gflag F F1 ≠ 0) : LinearIndependent E (tupMU F F1 M U) := by
  have hli := PI.PairCorankPos.W.linIndep F F1 hG
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg
  have hsum : ∑ i, g i • tupMU F F1 M U i =
      ∑ s, (Sum.elim (M *ᵥ fun a => g (Sum.inl a)) (U *ᵥ fun b => g (Sum.inr b)) s) •
        Sum.elim F.fvec F1.fvec s := by
    simp only [Fintype.sum_sum_type, tupMU, Sum.elim_inl, Sum.elim_inr, Finset.smul_sum, smul_smul, mulVec,
      dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => (U x y * g (Sum.inr y)) • F1.fvec x)]
    congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_ <;> rw [mul_comm]
  rw [hsum] at hg
  have h0 := hli _ hg
  have hMd : M.det ≠ 0 := by rw [upUni_det hM]; exact one_ne_zero
  have hUd : U.det ≠ 0 := by rw [upUni_det hU]; exact one_ne_zero
  have hl : (fun a => g (Sum.inl a)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hMd (funext fun a => h0 (Sum.inl a))
  have hr : (fun b => g (Sum.inr b)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hUd (funext fun b => h0 (Sum.inr b))
  intro s
  rcases s with a | b
  · exact congrFun hl a
  · exact congrFun hr b

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

