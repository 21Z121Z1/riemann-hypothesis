import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0555
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0167
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0552
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanCharacterTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder Kronecker Matrix

namespace GlobalTheory.BottomRealChar

open GlobalTheory.Grid (neg sgn ofSgn)

theorem detPlus_neg_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus (-1) 1 a b = 1 := by
  unfold GlobalTheory.WeilParts.detPlus
  have e : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have e2 : (1 / 2 : ℂ) • ((1 + -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * (b ⊗ₖ aᵀ)) +
      (1 / 2 : ℂ) • (1 - -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = 1 := by
    rw [add_neg_cancel, Matrix.zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    norm_num
  rw [e, e2, Matrix.det_one]

theorem commGroup_div_eq_div_mul_ratio {G : Type*} [CommGroup G] (a x y e c : G) :
    c * e / (a * x * e) = c * e / (a * y * e) * (y * x⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

def detChar {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) : GinfC V →* ℂ where
  toFun g := ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g.1)).det ^ e τ
  map_one' := by
    simp only [OneMemClass.coe_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, Finset.prod_const_one]
  map_mul' g h := by
    simp only [Subgroup.coe_mul, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]

theorem detChar_apply {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) (g : GinfC V) :
    detChar θ V e g = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g.1)).det ^ e τ := rfl

theorem continuous_detChar {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (e : D.what₂.Tau → ℤ) :
    Continuous (detChar θ V e) := by
  refine continuous_finset_prod _ fun τ _ => Continuous.zpow₀ ?_ _ fun g => Or.inl fun h0 => ?_
  · exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
      ((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_subtype_val))).matrix_det
  · have := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g.1)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this

theorem isAlgebraic_detChar {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) (g : GinfC V)
    (hg : ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)) : IsAlgebraic ℚ (detChar θ V e g) := by
  let K := algebraicClosure ℚ ℂ
  have hK : ∀ z : ℂ, z ∈ K ↔ IsAlgebraic ℚ z := fun z => mem_algebraicClosure_iff
  rw [← hK, detChar_apply]
  refine prod_mem fun τ _ => zpow_mem ?_ _
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => (hK _).2 (hg τ _ _))

theorem exists_realChar : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X → ∃ χ : GinfC A →* ℂ, Continuous χ ∧ (∀ (t : T) (g : GinfC A), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g.1, 1) (X.f t) = χ g • X.f t) ∧ ∀ g : GinfC A, (∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)) → IsAlgebraic ℚ (χ g) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hW := fun t => hI.weil t
  have hxi : ∀ t τ, HasInfExp D (L.xi t) τ 0 := fun t τ => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    exact GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  choose b hb using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ WW.rank τ hθ (hW μ₀).hecT (hW μ₀).resT
  have hbt : ∀ t τ, HasInfExp D ((G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2))) τ (b τ) := by
    intro t τ
    have hrel : (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) / (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) =
        (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) / (L.mu μ₀ (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) *
          (L.xi μ₀ * (L.xi t)⁻¹) := by
      simp only [LevCh.mu, Lift.tup]
      exact commGroup_div_eq_div_mul_ratio _ _ _ _ _
    rw [hrel]
    have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hb τ)
      (GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hxi μ₀ τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hxi t τ)))
    simpa using this
  choose k hk using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ WW.rank τ (b τ) (hW μ₀).hecT (hW μ₀).resT (hb τ)
  refine ⟨detChar W.θ A fun τ => -(k τ - WW.rank), continuous_detChar hθ _ _, fun t g => ?_,
    fun g hg => isAlgebraic_detChar _ _ _ g hg⟩
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := by
    have hne : X.ideal (locPl G) t ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
    obtain ⟨f, h1, h2⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D W.ψ W.θ A WW X.rA X.rW _ _ _ _ _ hI.rigA hI.rigW (hI.weil' t).hecT
      (hI.idem t) hne hI.isVac
    obtain ⟨Tm, hT⟩ := h1.1
    exact ((hI.fst t).2 Tm hT).trans (h1.2 Tm hT).symm ▸ h2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst t)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have hg' : (ofSgn true A).symm g.1 ∈ GinfC (neg A) :=
    (GlobalTheory.SgnIdent.mem_GinfC_sgn true A _).2 (by rw [MulEquiv.apply_symm_apply]; exact g.2)
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g.1) = Formalism.L2.Theta.mt A g.1 := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (neg A) hdet _ hg'
  have hy1 : IsDetRoot WW 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_one W.θ τ WW
  rw [GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ _ η hη (hW t) (fun τ => -X.rA.s τ) X.rW.s cS cT
      _ hg' 1 (one_mem _) (fun τ => by rw [hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy1 (X.f t) hf hfock]
  congr 1
  have hx' : ∀ τ, HasInfExp D (((G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2))) * (η ^ WW.rank)⁻¹) τ ((k τ - WW.rank : ℤ) : ℚ) := fun τ => by
    have e : ((k τ - WW.rank : ℤ) : ℚ) = b τ - (WW.rank : ℚ) / 2 := by push_cast; rw [hk]; ring
    rw [e]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (hbt t τ) (hη.2.2.2 τ) _
  simp only [hsA, hsW, detPlus_neg_one_one, Finset.prod_const_one, mul_one, map_one]
  rw [Circle.coe_inv, hxv _ (fun τ => k τ - WW.rank) hx', ← Finset.prod_inv_distrib, detChar_apply, hmt]
  exact Finset.prod_congr rfl fun τ _ => (_root_.zpow_neg _ _).symm

end GlobalTheory.BottomRealChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinOfRest
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaSchrCont

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic
open scoped Matrix

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finSlice (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun w => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), w i)

theorem finSlice_mem {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    finSlice Φ y ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    have : finSlice (pureA F f g) y = f y • g := by
      funext w
      simp only [finSlice, pureA, RingEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ hg
  | zero => exact (SB _).zero_mem
  | add x x' _ _ hx hx' => exact (SB _).add_mem hx hx'
  | smul a x _ hx => exact (SB _).smul_mem a hx

theorem exists_fin_of_rest {f : SInf F κ} {r : (κ → AF F) → ℂ} (hr : Rest (evI F) (⇑f) r) (hf : f ≠ 0) :
    ∃ G ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∀ x : κ → AF F, r x = G fun i => (x i).2 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  refine ⟨(f y)⁻¹ • finSlice (tens (evI F) (⇑f) r) y, Submodule.smul_mem _ _ (finSlice_mem hr.2 y), fun x => ?_⟩
  let z : κ → AF F := fun i => mk (e.symm (y i) - (x i).1) 0
  have hz : At (evI F) z := by
    intro u hu
    funext i
    exact at_mk _ u hu
  have hxz : x + z = fun i => (e.symm (y i), (x i).2) := by
    funext i
    refine Prod.ext ?_ ?_
    · show (x i).1 + (e.symm (y i) - (x i).1) = e.symm (y i)
      abel
    · show (x i).2 + 0 = (x i).2
      exact add_zero _
  have h1 := hr.1 x z hz
  rw [hxz] at h1
  have h2 : (fun i => evI F ((e.symm (y i), (x i).2) : AF F)) = y := by
    funext i
    exact e.apply_symm_apply (y i)
  simp only [Pi.smul_apply, smul_eq_mul, finSlice, tens]
  rw [h2, ← h1]
  field_simp
  rfl

theorem tens_eq_pureA (g : SInf F κ) {r : (κ → AF F) → ℂ} {G : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hG : ∀ x : κ → AF F, r x = G fun i => (x i).2) : tens (evI F) (⇑g) r = pureA F g G := by
  funext x
  simp only [tens, pureA, hG]
  rfl

theorem schr_pureA_eq [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsStd ψ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
    let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
    schr ψ w (pureA F f g) = pureA F (archS f (fun i => q (w.2 i)) (fun i => q (w.1 i))
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)))
      (finS ψ g (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)) := by
  intro q h
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  funext x
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add, RingHom.map_dotProduct]
        rfl
      rw [e1, map_add, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add, RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

theorem exists_clm_hasSum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    Rest (evI F) (⇑f) r → f ≠ 0 → ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ g : SInf F (Fin n × Fin d),
      HasSum (fun ξ : Fin n × Fin d → F => M.co.rho ψ u (tens (evI F) (⇑g) r) (fun i => algebraMap F (AF F) (ξ i))) (T g) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ u f r hr hf
  obtain ⟨G, hG, hrG⟩ := exists_fin_of_rest hr hf
  set w := M.co.e u with hw
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let G' := finS ψ G (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)
  have hG' : G' ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := finS_mem ψ hψ.1 hG _ _ _
  obtain ⟨l, hl, hleq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  obtain ⟨T₀, hT₀⟩ := hl G' hG'
  let A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
    (SchwartzMap.smulLeftCLM ℂ (fun y : Fin n × Fin d → mixedEmbedding.mixedSpace F => eChar ((-trL c) y + -k))).comp
      (SchwartzMap.compSubConstCLM ℂ (-t))
  refine ⟨T₀.comp A, fun g => ?_⟩
  have hΦ : M.co.rho ψ u (tens (evI F) (⇑g) r) = pureA F (A g) G' := by
    rw [tens_eq_pureA g hrG]
    exact schr_pureA_eq ψ hψ w g G
  rw [hΦ]
  have hmem : pureA F (A g) G' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨A g, G', hG', rfl⟩
  convert hasSum_thetaSum F hmem using 1
  rw [ContinuousLinearMap.comp_apply, ← hT₀, hleq _ hmem]

end GlobalTheory.ThetaSchrCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierIndexRationalPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

theorem std_eq_colLat_one' {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

theorem even_bot' {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

theorem vac_jet_ne_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hX : IsBottomTri W i j X) :
    ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac
      (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set f : WO A WW → ℂ := fun w => starRingEnd ℂ (X.vac w) with hfdef
  have hf0 : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s X.rA.Λ X.rW.Λ f :=
    GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
  have hf : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s (colLat (1 : GL (Fin A.rank) D.host.E) : Set _)
      (colLat (1 : GL (Fin WW.rank) D.host.E) : Set _) f := by
    rw [← std_eq_colLat_one' X.rA.Λ hX.std.2.1, ← std_eq_colLat_one' X.rW.Λ hX.stdW.2.1]
    exact hf0
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin A.rank) D.host.E).1 * A.gram *
      (1 : GL (Fin A.rank) D.host.E).1 = 1 := by
    rw [hX.std.1]
    simp [Formalism.UG.cT]
  have hW : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin WW.rank) D.host.E).1 * WW.gram *
      (1 : GL (Fin WW.rank) D.host.E).1 = 1 := by
    rw [hX.stdW.1]
    simp [Formalism.UG.cT]
  have hcA : ∀ τ, IsCartanInv (gramAt D A τ) (X.rA.s τ) := fun τ => (hIs.rigA.2.2 τ).1
  have hcW : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hIs.rigW.2.2 τ).1
  have hBA : (fun τ => (1 : GL (Fin A.rank) D.host.E).1.map (tauE D τ)) = X.rA.B := by
    funext τ
    rw [(hX.std.2.2 τ).2]
    simp
  have hBW : (fun τ => (1 : GL (Fin WW.rank) D.host.E).1.map (tauE D τ)) = X.rW.B := by
    funext τ
    rw [(hX.stdW.2.2 τ).2]
    simp
  obtain ⟨δ, hC, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex D.host.ccK δ hC).1
  obtain ⟨e0, he0, he0ne⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hC t0 ht0 A.rank WW.rank (even_bot' hX)
  obtain ⟨c, hc⟩ := GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ
    ht0 e0 he0 f hf
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D he0.1.1 he0ne
  refine ⟨α, ?_⟩
  change pureTensorO W.ψ W.θ (negSp A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial α 1) 0 ≠ 0
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial W.ψ W.θ A WW X.rA.s X.rW.s X.rA.B X.rW.B X.vac hψ hθ α 0, map_ne_zero,
    ← hBA, ← hBW, hc α, GlobalTheory.FockPos.applyAt0_monomial']
  have hprod : (α.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  exact mul_ne_zero c.ne_zero (mul_ne_zero hprod (mul_ne_zero hfac hα))

end GlobalTheory.MovedJetNZ

end

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

theorem moved_vac_jet_ne_zero : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ hI _ hX t γ hγ _ _ γ' hγ' _ _ _ _
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set om' := (X.ω t).toSgn true with hom'
  have hom := hIs.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => by rw [(hX.std.2.2 τ).2]
  obtain ⟨k₀, hk₀⟩ := vac_jet_ne_zero hI hX
  by_contra hall
  push_neg at hall
  set γs := (ofSgn true A).symm γ with hγs
  have hγsQ : γs ∈ GQ (neg A) :=
    (GlobalTheory.SgnIdent.mem_GQ_sgn true A γs).2 (by rw [hγs, MulEquiv.apply_symm_apply]; exact hγ)
  have hg : X.ω t (γ, γ') X.vac = om' (γs, γ') X.vac := by
    show _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm γ), γ') X.vac
    rw [MulEquiv.apply_symm_apply]
  simp only [hg] at hall
  have hvθ : IsThetaFunO W.ψ (neg A) WW X.vac := hIs.isVac.2.theta
  have hgθ : IsThetaFunO W.ψ (neg A) WW (om' (γs, γ') X.vac) := hom.om_pres _ _ hvθ
  have hzero : ∀ P, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (om' (γs, γ') X.vac) P 0 = 0 := by
    intro P
    rw [P.as_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have e : MvPolynomial.monomial k (P.coeff k) = P.coeff k • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Pi.smul_apply, hall k, smul_zero]
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ om' hom hθ (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ)
    X.rA.B (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) X.rW.s X.rW.s X.rW.B
    (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) γs γ' (fun τ => by rw [hsA]; simp) (fun τ => by rw [hsW]; simp)
    (fun τ => rfl) (fun τ => rfl) X.vac hvθ (MvPolynomial.monomial k₀ 1)
  have haut := hom.om_aut γs hγsQ γ' hγ' _ hop.1
  apply hk₀
  rw [← haut, hop.2]
  have hBW : ∀ τ, X.rW.B τ = 1 := fun τ => by rw [(hX.stdW.2.2 τ).2]
  have e1 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) =
      fun τ => X.rA.B τ * compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) := by
    funext τ; rw [hBA, Matrix.mul_one, Matrix.one_mul]
  have e2 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) =
      fun τ => X.rW.B τ * compAt W.θ τ (Formalism.L2.Theta.mt WW γ') := by
    funext τ; rw [hBW, Matrix.mul_one, Matrix.one_mul]
  have es : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have et : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  rw [e1, e2]
  rw [es, et] at hzero ⊢
  change pureTensorO W.ψ W.θ (negSp A) WW (fun _ => -1) (fun _ => 1) _ _ _ _ _ = _
  rw [GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ _ _ _ _ _ hgθ]
  exact hzero _

end GlobalTheory.MovedJetNZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingMemStabilizerAuxiliaryLatticeStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEmbedding_mem_stabilizer_auxiliaryLattice : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (y : GfC A), Lev.finE A y.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) Λ) → Lev.finE B (finEmb d y).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) := by
  first | exact @GlobalTheory.FinEmbLat.finEmb_mem_stabGL | exact GlobalTheory.FinEmbLat.finEmb_mem_stabGL | (intros; apply GlobalTheory.FinEmbLat.finEmb_mem_stabGL <;> assumption)
end
end

