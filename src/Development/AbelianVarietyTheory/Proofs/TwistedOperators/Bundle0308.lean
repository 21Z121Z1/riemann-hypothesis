import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin)
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LowerMembers

theorem pairing_eq_zero : ∀ (X : ProvA), Formalism.MainNotions.SchurIrreducible.admQ5 X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → ∀ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de → (∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → ∀ i : ℕ, 1 ≤ i → i ≤ al.length + be.length → i ≤ ga.length + de.length → ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (e : Ix (al.length + be.length - i) (ga.length + de.length - i) ≃ Fin V.rank) (e' : Ix (al.length + de.length + t) (ga.length + be.length) ≃ Fin W.rank) (m' : ℤ) (aS : ℚ) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] (X.ds _ _ (lamA' t al be ga de)).U.H) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) (b : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] ℂ), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat (M'.ε τ) e' → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches (X.ds _ _ (lamA' t al be ga de)) M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → GlobalTheory.Chain.IoLift.IsKAct M' τ a' → (∀ Y ∈ lieAt W τ, ∀ P y, b (locT ε (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y + b P (a' Y y) = 0) → b = 0 := by
  intro X h5 hAR t al be ga de hd hbig i hi hip hiq D V W S' M' τ ε e e' m' aS U' a' b he he' hm' h₂ ha hb
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ ε (M'.ε τ) e e' he he'
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm ((X.ds _ _ (lamA' t al be ga de)).ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : (X.ds _ _ (lamA' t al be ga de)).HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm ((X.ds _ _ (lamA' t al be ga de)).ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = (X.ds _ _ (lamA' t al be ga de)).ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  let B' : Pol _ _ _ _ →ₗ[ℂ] (X.ds _ _ (lamA' t al be ga de)).HK.V →ₛₗ[starRingEnd ℂ] ℂ :=
    { toFun := fun P => (b (κ.symm P)).comp j
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  have hB' : ∀ P v, B' (κ P) v = b P (j v) := fun P v => by simp [B']
  have h0 : B' = 0 := GlobalTheory.T.no_invariant_pairing_smaller_fock_source X h5 hAR t al be ga de hd hbig i hi hip hiq B' (fun Y hY P y => by
    obtain ⟨P, rfl⟩ := κ.surjective P
    have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
    have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
    have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j ((X.ds _ _ (lamA' t al be ga de)).HK.act Y y) -
        ((aS : ℂ) * Y.trace) • j y := by
      have h7 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
          j ((X.ds _ _ (lamA' t al be ga de)).HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
        refine Subtype.ext (U'.injective ?_)
        rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
      rw [h7, map_add, LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
        sub_eq_add_neg, ← neg_smul]
      congr 2
      ring
    have h := hb _ hY' P (j y)
    rw [h6, fr_toFrame, trace_toFrame, h4] at h
    rw [← hκ.2, hB', hB', ← h]
    simp [plainMat])
  refine LinearMap.ext fun P => LinearMap.ext fun z => ?_
  obtain ⟨v, rfl⟩ := hsurj z
  rw [← hB', h0]
  rfl

end GlobalTheory.LowerMembers

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalCongruenceMemLatticeCongruenceLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CongLevelInst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_hatL_iff (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) :
    x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ x ∈ Formalism.MainNotions.S.lamAf (F := F) Λ := by
  show x ∈ Submodule.span _ _ ↔ x ∈ Submodule.span _ _
  rw [Set.image_eq_range]
  rfl

theorem natCast_smul_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (g : ℕ)
    (z : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ((g : E ⊗[F] Formalism.MainNotions.S.Af F)) • z ∈ Formalism.L2.Herm.hatL (F := F) (Ideal.span {((g : ℕ) : 𝓞 E)} • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨((g : ℕ) : 𝓞 E) • l, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl, ?_⟩
    funext i
    have h1 : ((g : ℕ) : 𝓞 E) • l i = (g : E) * l i := by
      rw [Algebra.smul_def]; simp
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1, map_mul, map_natCast]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

theorem mem_congLev (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (g : ℕ)
    (k : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) (hU : k ∈ Formalism.UG.UPts hc.sig J (Formalism.MainNotions.S.Af F))
    (hs : k ∈ Formalism.UG.stabGL (Formalism.MainNotions.S.lamAf (F := F) Λ))
    (hd : ∀ y ∈ Formalism.MainNotions.S.lamAf (F := F) Λ, ∃ z ∈ Formalism.MainNotions.S.lamAf (F := F) Λ,
      ((k : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) - 1) *ᵥ y = (g : E ⊗[F] Formalism.MainNotions.S.Af F) • z) :
    k ∈ congLev hc J Λ (Ideal.span {((g : ℕ) : 𝓞 E)}) := by
  refine ⟨hU, ?_, ?_⟩
  · intro x
    rw [mem_hatL_iff, mem_hatL_iff]
    exact hs x
  · intro x hx
    obtain ⟨z, hz, e⟩ := hd x ((mem_hatL_iff Λ x).1 hx)
    have e2 : (k : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) *ᵥ x - x = (g : E ⊗[F] Formalism.MainNotions.S.Af F) • z := by
      rw [← e, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e2]
    exact natCast_smul_mem_hatL Λ g z ((mem_hatL_iff Λ z).2 hz)

end GlobalTheory.CongLevelInst

namespace GlobalTheory.CongLevelInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem kg_mem_levA : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (g : ℕ), 1 ≤ g → ∀ k ∈ (Formalism.IndefR.Eqv.UI.instV fr).Kg g, Formalism.IndefR.Eqv.UI.brg fr (1, k) ∈ Formalism.IndefR.Lev.levA V (congLev D.sp.cm V.gram fr.Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})) := by
  intro D V fr g _ k hk
  rw [Formalism.IndefR.Eqv.brg_mem_levA]
  exact ⟨rfl, mem_congLev D.sp.cm V.gram fr.Λ g k.1 k.2 hk.1 hk.2⟩

end GlobalTheory.CongLevelInst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdUpdateSelf
section
noncomputable section

open scoped TensorProduct Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.TensorContraction

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem prod_update_self [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∉ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = ∏ k ∈ s, φ k (v k) := by
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : k ≠ j := fun e => hj (e ▸ hk)
  rw [Function.update_of_ne hk']

theorem prod_update_mem [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∈ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = φ j x * ∏ k ∈ s.erase j, φ k (v k) := by
  rw [← Finset.mul_prod_erase s _ hj, Function.update_self,
    prod_update_self φ (s.erase j) j (Finset.notMem_erase j s) v x]

def contrM (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (i : ι) (hi : i ∉ s) (hs : ∀ j, j ≠ i → j ∈ s) :
    MultilinearMap ℂ K (K i) where
  toFun v := (∏ k ∈ s, φ k (v k)) • v i
  map_update_add' v j x y := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self, smul_add]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_add, add_mul, add_smul]
  map_update_smul' v j c x := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self]
      rw [smul_comm]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul,
        mul_assoc, mul_smul]

def contrL (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) : (⨂[ℂ] j, K j) →ₗ[ℂ] K i :=
  PiTensorProduct.lift (contrM φ (Finset.univ.erase i) i (Finset.notMem_erase _ _)
    fun j h => Finset.mem_erase.2 ⟨h, Finset.mem_univ j⟩)

theorem contrL_tprod (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (v : ∀ j, K j) :
    contrL φ i (PiTensorProduct.tprod ℂ v) = (∏ k ∈ Finset.univ.erase i, φ k (v k)) • v i := by
  rw [contrL, PiTensorProduct.lift.tprod]
  rfl

theorem contrL_comp_mapFactor (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (f : Module.End ℂ (K i)) :
    contrL φ i ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ contrL φ i := by
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun v => ?_
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, contrL_tprod]
  rw [prod_update_self φ _ i (Finset.notMem_erase i _), Function.update_self, map_smul]

private theorem eq_zero_of_contrL_eq_zero (i : ι) (z : ⨂[ℂ] j, K j)
    (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i z = 0) : z = 0 := by
  let b : ∀ j, Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ (K j)) ℂ (K j) :=
    fun j => Module.Basis.ofVectorSpace ℂ (K j)
  let B := Basis.piTensorProduct b
  refine B.forall_coord_eq_zero_iff.1 fun p => ?_
  let φ : ∀ j, K j →ₗ[ℂ] ℂ := fun j => (b j).coord (p j)
  have key : B.coord p = (b i).coord (p i) ∘ₗ contrL φ i := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext fun v => ?_
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contrL_tprod, map_smul, smul_eq_mul, Module.Basis.coord_apply, B,
      Basis.piTensorProduct_repr_tprod_apply, φ]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [key, LinearMap.comp_apply, h φ, map_zero]

theorem eq_of_contrL (i : ι) (x y : ⨂[ℂ] j, K j) (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x = contrL φ i y) :
    x = y := by
  rw [← sub_eq_zero]
  exact eq_zero_of_contrL_eq_zero i (x - y) fun φ => by rw [map_sub, h φ, sub_self]

private theorem piTensorProduct_map_ite_eq_self_of_slot_fixed (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j)
    (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) (s : Finset ι) :
    PiTensorProduct.map (fun j => if j ∈ s then p j else LinearMap.id) x = x := by
  induction s using Finset.induction_on with
  | empty => simp [PiTensorProduct.map_id]
  | insert a s ha ih =>
    have e : (fun j => if j ∈ insert a s then p j else (LinearMap.id : Module.End ℂ (K j))) =
        fun j => Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) a (p a) j ∘ₗ
          (if j ∈ s then p j else LinearMap.id) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha]
      · simp [hj]
    rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
    exact h a

theorem map_eq_self (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j) (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) :
    PiTensorProduct.map p x = x := by
  simpa using piTensorProduct_map_ite_eq_self_of_slot_fixed p x h Finset.univ

theorem mem_range_map (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ (i : ι) (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by

  have hN : ∀ i, ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x ∈ N i :=
    fun i φ => h i (contrL φ i) (contrL_comp_mapFactor φ i)

  choose g hg using fun i => LinearMap.exists_leftInverse_of_injective (N i).subtype (N i).ker_subtype
  let P : ∀ i, Module.End ℂ (K i) := fun i => (N i).subtype ∘ₗ g i
  have hP : ∀ i, ∀ v ∈ N i, P i v = v := fun i v hv => by
    have := congrArg (fun f => (N i).subtype (f ⟨v, hv⟩)) (hg i)
    simpa [P] using this

  have hfix : ∀ i, intersection_update_fsHerm_neg_one i (P i) x = x := fun i =>
    eq_of_contrL i _ _ fun φ => by
      rw [← LinearMap.comp_apply (contrL φ i), contrL_comp_mapFactor, LinearMap.comp_apply, hP i _ (hN i φ)]
  rw [LinearMap.mem_range]
  refine ⟨PiTensorProduct.map g x, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  exact map_eq_self P x hfix

end GlobalTheory.TensorContraction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjXPreservesEmbeddingLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proj_X_preserves_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e * d.qX) *ᵥ v ∈ a.lat Λ 𝔟 := by
  first | exact @GlobalTheory.projX_embedding_lattice | exact GlobalTheory.projX_embedding_lattice | (intros; apply GlobalTheory.projX_embedding_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjYPreservesEmbeddingLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proj_Y_preserves_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e' * d.qY) *ᵥ v ∈ a.lat Λ 𝔟 := by
  first | exact @GlobalTheory.AscFin.projY_mem_lat | exact GlobalTheory.AscFin.projY_mem_lat | (intros; apply GlobalTheory.AscFin.projY_mem_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientTraceInfinitesimalStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudocoefficient_trace_infinitesimal : GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.HarishChandraCharacters → ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (hδ : IsURepOn (UJset ε) δ), HasInfChar ε χ δ → ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ (ujRep hδ) f → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ), HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 → HasInfChar ε χ π := by
  first | exact @GlobalTheory.TraceInfChar.hasInfChar_of_trace_ne_zero | exact GlobalTheory.TraceInfChar.hasInfChar_of_trace_ne_zero | (intros; apply GlobalTheory.TraceInfChar.hasInfChar_of_trace_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RapidDecayAllRealCoordinatesOfFunctionals
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DecayCoord

theorem theta_incA {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : D.host.E) :
    θ τ (infPart D (incA D x)) = tauE D τ x := by
  have h : infPart D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x := by
    simp [infPart, incA, inclR, Algebra.TensorProduct.map_tmul]
  rw [h]
  exact (hθ τ).1 x

theorem compAt_emb {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V W : HSp D) {a b : ℕ}
    (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y : Mx D a b) :
    compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y) = P.map (tauE D τ) * compAt θ τ y * Q.map (tauE D τ) := by
  have hm : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)), compAt θ τ M = M.map ((θ τ).comp (infPart D)) :=
    fun M => rfl
  have hE : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      (M.map (incA D)).map ((θ τ).comp (infPart D)) = M.map (tauE D τ) := by
    intro m n M; ext i j; simp [theta_incA θ hθ]
  rw [hm, hm, GlobalTheory.IsoMean.emb, Matrix.map_mul, Matrix.map_mul, hE, hE]

theorem exists_left_inv {K : Type*} [Field K] {n a : ℕ} (P : Matrix (Fin n) (Fin a) K) (hP : P.rank = a) :
    ∃ P' : Matrix (Fin a) (Fin n) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [Matrix.rank] at hP
    rw [hP, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h2 := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h2
  have h3 : LinearMap.toMatrix' P.mulVecLin = P := LinearMap.toMatrix'_toLin' P
  rwa [h3] at h2

theorem exists_right_inv {K : Type*} [Field K] {n b : ℕ} (Q : Matrix (Fin b) (Fin n) K) (hQ : Q.rank = b) :
    ∃ Q' : Matrix (Fin n) (Fin b) K, Q * Q' = 1 := by
  obtain ⟨R, hR⟩ := exists_left_inv Qᵀ (by rw [Matrix.rank_transpose, hQ])
  refine ⟨Rᵀ, ?_⟩
  have := congrArg Matrix.transpose hR
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem sum_pow_le {κ : Type*} [Fintype κ] [Nonempty κ] (u : κ → ℝ) (hu : ∀ k, 0 ≤ u k) (N : ℕ) :
    (∑ k, u k) ^ N ≤ (Fintype.card κ : ℝ) ^ N * ∑ k, u k ^ N := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  have h1 : ∑ k, u k ≤ Fintype.card κ * u j := by
    have := Finset.sum_le_card_nsmul Finset.univ u (u j) (fun k _ => hj k (Finset.mem_univ _))
    simpa [nsmul_eq_mul] using this
  calc (∑ k, u k) ^ N ≤ (Fintype.card κ * u j) ^ N :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => hu k) h1 N
    _ = (Fintype.card κ : ℝ) ^ N * u j ^ N := mul_pow _ _ _
    _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (f := fun k => u k ^ N) (fun k _ => pow_nonneg (hu k) N) (Finset.mem_univ j)

theorem trace_single {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℂ) (k : Fin a) (l : Fin b) (α : ℂ) :
    (Yᴴ * Matrix.single k l α).trace = star (Y k l) * α := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single l, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp
  · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hi]
  · simp

theorem norm_le_re (c w : ℂ) (hc : c ≠ 0) :
    ‖w‖ ≤ |2 * (c * (star w * c⁻¹)).re| + |2 * (c * (star w * (Complex.I * c⁻¹))).re| := by
  have e1 : c * (star w * c⁻¹) = star w := by field_simp
  have e2 : c * (star w * (Complex.I * c⁻¹)) = Complex.I * star w := by field_simp
  rw [e1, e2]
  have := Complex.norm_le_abs_re_add_abs_im w
  simp only [Complex.star_def, Complex.conj_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_im, abs_mul]
  norm_num
  linarith [abs_nonneg w.re, abs_nonneg w.im]

end GlobalTheory.DecayCoord

namespace GlobalTheory.DecayCoord

theorem det_gramAt_ne {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ).det ≠ 0 := by
  unfold gramAt
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (GlobalTheory.StabCompact.det_gram_ne_zero V)

theorem herm_key {D : D7} (V W : HSp D) (τ : D.what₂.Tau) {a b : ℕ} (Pc : Matrix (Fin W.rank) (Fin a) ℂ)
    (Pl : Matrix (Fin a) (Fin W.rank) ℂ) (hP : Pl * Pc = 1) (Qc : Matrix (Fin b) (Fin V.rank) ℂ)
    (Qr : Matrix (Fin V.rank) (Fin b) ℂ) (hQ : Qc * Qr = 1) (Y X : Matrix (Fin a) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt V W τ ((gramAt D W τ)⁻¹ * Plᴴ * X * Qrᴴ * gramAt D V τ) (Pc * Y * Qc) =
      (Yᴴ * X).trace := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  set GV := gramAt D V τ
  set GW := gramAt D W τ
  have hW : GW * GW⁻¹ = 1 := Matrix.mul_nonsing_inv GW (Ne.isUnit (det_gramAt_ne W τ))
  have hV : GV * GV⁻¹ = 1 := Matrix.mul_nonsing_inv GV (Ne.isUnit (det_gramAt_ne V τ))
  have hP' : Pcᴴ * Plᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hP, Matrix.conjTranspose_one]
  have hQ' : Qrᴴ * Qcᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
  have e : GV⁻¹ * (Pc * Y * Qc)ᴴ * GW * (GW⁻¹ * Plᴴ * X * Qrᴴ * GV) = GV⁻¹ * ((Qcᴴ * Yᴴ * X * Qrᴴ) * GV) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc GW GW⁻¹, hW, Matrix.one_mul, ← Matrix.mul_assoc Pcᴴ Plᴴ, hP', Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc _ GV, hV, Matrix.mul_one, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul]

end GlobalTheory.DecayCoord

namespace GlobalTheory.DecayCoord

theorem decay_real_coords : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, (∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ y : Mx D a b, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y))| ^ m * ‖f y‖ ≤ C) → ∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C := by
  intro D V W a b P Q hP hQ θ hθ f hf N
  classical
  obtain ⟨Pl, hPl⟩ := exists_left_inv P hP
  obtain ⟨Qr, hQr⟩ := exists_right_inv Q hQ
  have hPlτ : ∀ τ, Pl.map (tauE D τ) * P.map (tauE D τ) = 1 := fun τ => by
    rw [← Matrix.map_mul, hPl, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQrτ : ∀ τ, Q.map (tauE D τ) * Qr.map (tauE D τ) = 1 := fun τ => by
    rw [← Matrix.map_mul, hQr, Matrix.map_one _ (map_zero _) (map_one _)]
  let c : D.what₂.Tau → ℂ := fun τ => tauE D τ D.host.xi0
  have hc : ∀ τ, c τ ≠ 0 := fun τ => (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  let zOf : D.what₂.Tau → Matrix (Fin a) (Fin b) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ := fun τ X =>
    (gramAt D W τ)⁻¹ * (Pl.map (tauE D τ))ᴴ * X * (Qr.map (tauE D τ))ᴴ * gramAt D V τ
  let zι : D.what₂.Tau × Fin a × Fin b × Bool → Matrix (Fin W.rank) (Fin V.rank) ℂ := fun i =>
    zOf i.1 (Matrix.single i.2.1 i.2.2.1 (if i.2.2.2 then Complex.I * (c i.1)⁻¹ else (c i.1)⁻¹))
  let ℓ : D.what₂.Tau × Fin a × Fin b × Bool → Mx D a b → ℝ := fun i y =>
    |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W i.1 (zι i) (compAt θ i.1 (GlobalTheory.IsoMean.emb V W P Q y))|
  have hterm : ∀ (y : Mx D a b) (τ : D.what₂.Tau) (k : Fin a) (l : Fin b),
      ‖θ τ (infPart D (y k l))‖ ≤ ∑ β : Bool, ℓ (τ, k, l, β) y := by
    intro y τ k l
    have hs : ∀ α : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ (zOf τ (Matrix.single k l α))
        (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y)) = 2 * (c τ * (star (compAt θ τ y k l) * α)).re := by
      intro α
      rw [compAt_emb θ hθ τ V W P Q y]
      show 2 * (c τ * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt V W τ _ _).re = _
      rw [herm_key V W τ _ _ (hPlτ τ) _ _ (hQrτ τ), trace_single]
    rw [Fintype.sum_bool]
    simp only [ℓ, zι, if_true, if_false, Bool.false_eq_true]
    rw [hs, hs]
    have := norm_le_re (c τ) (compAt θ τ y k l) (hc τ)
    rw [add_comm]
    exact this
  have hS : ∀ y : Mx D a b, (∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ≤ ∑ i, ℓ i y := by
    intro y
    simp only [Fintype.sum_prod_type]
    gcongr with τ _ k _ l _
    exact hterm y τ k l
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨C0, hC0⟩ := hf τ0 0 0
  choose Cf hCf using fun i : D.what₂.Tau × Fin a × Fin b × Bool => hf i.1 (zι i) N
  refine ⟨(Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N * (C0 + ∑ i, Cf i), fun y => ?_⟩
  let u : Option (D.what₂.Tau × Fin a × Fin b × Bool) → ℝ := fun o => o.elim 1 fun i => ℓ i y
  have hu : ∀ o, 0 ≤ u o := fun o => by cases o <;> simp [u, ℓ]
  have hsum : ∑ o, u o = 1 + ∑ i, ℓ i y := by rw [Fintype.sum_option]; rfl
  have hpow : ∑ o, u o ^ N = 1 + ∑ i, ℓ i y ^ N := by rw [Fintype.sum_option]; simp [u]
  have hS0 : 0 ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖ := by positivity
  have hf0 : 0 ≤ ‖f y‖ := norm_nonneg _
  have hC0' : ‖f y‖ ≤ C0 := by simpa using hC0 y
  have hCf' : ∑ i, ℓ i y ^ N * ‖f y‖ ≤ ∑ i, Cf i := Finset.sum_le_sum fun i _ => hCf i y
  calc (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖
      ≤ (1 + ∑ i, ℓ i y) ^ N * ‖f y‖ := by gcongr; exact hS y
    _ = (∑ o, u o) ^ N * ‖f y‖ := by rw [hsum]
    _ ≤ ((Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N * ∑ o, u o ^ N) * ‖f y‖ := by
        gcongr; exact sum_pow_le u hu N
    _ = (Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N *
          (‖f y‖ + ∑ i, ℓ i y ^ N * ‖f y‖) := by rw [hpow, ← Finset.sum_mul]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.DecayCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedHomLatticeSelfStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual : ∀ {D : D7} {S S' T T' : HSp D} {LS : Lat S} {LS' : Lat S'} {LT : Lat T} {LT' : Lat T'}, IsSelfDualC S LS → IsSelfDualC S' LS' → IsSelfDualC T' LT' → ∀ (j : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E), (∀ y ∈ LS', j *ᵥ y ∈ LS) → (∀ t ∈ LT, q *ᵥ t ∈ LT') → ∀ x : WO S T, x ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) → (rat q * x * rat j : WO S' T') ∈ latO S' T' (LS' : Set _) (LT' : Set _) (fun _ => True) := by
  first | exact @GlobalTheory.Twist.RatLatO.rat_mul_mem_latO | exact GlobalTheory.Twist.RatLatO.rat_mul_mem_latO | (intros; apply GlobalTheory.Twist.RatLatO.rat_mul_mem_latO <;> assumption)
end
end

