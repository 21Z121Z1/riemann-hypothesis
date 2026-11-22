import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0188

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionCuspidalParabolicProduct
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.HCInduction

open Formalism.L2.DIV GlobalTheory.BI

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem parab_eq_blockTri (b : Fin r → Fin s) :
    parab K b = blockTri (κ := K) (fun i => (b i : ℕ)) := by
  ext g
  constructor
  · intro hg
    exact hg.1
  · intro hg
    exact ⟨hg, (blockTri (κ := K) (fun i => (b i : ℕ))).inv_mem hg⟩

omit [Fintype K] [DecidableEq K] in

def blockGL (b : Fin r → Fin s) (c : Fin s) :
    GL (Fin (Fintype.card {i // b i = c})) K ≃* GL {i // b i = c} K :=
  glEquiv K (Fintype.equivFin {i // b i = c}).symm

omit [Fintype K] [DecidableEq K] in
theorem blockGL_apply (b : Fin r → Fin s) (c : Fin s) (g : GL (Fin (Fintype.card {i // b i = c})) K)
    (x y : {i // b i = c}) :
    ((blockGL b c g : GL {i // b i = c} K) : Matrix _ _ K) x y =
      (g : Matrix _ _ K) (Fintype.equivFin _ x) (Fintype.equivFin _ y) := rfl

theorem sum_unipRadical_eq_zero (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K))
    (hτ : IsCuspidal K τ) (c' : Fin (Fintype.card {i // b i = c}) → ℕ) (hc' : ∃ i j, c' i ≠ c' j) :
    ∑ᶠ u : GlobalTheory.FiniteGL.unipRadical K c', LinearMap.trace ℂ τ (τ.ρ (blockGL b c u)) = 0 := by
  classical
  let _ : Fintype (GlobalTheory.FiniteGL.unipRadical K c') := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  let ρu : Representation ℂ (GlobalTheory.FiniteGL.unipRadical K c') τ :=
    τ.ρ.comp ((blockGL b c).toMonoidHom.comp (GlobalTheory.FiniteGL.unipRadical K c').subtype)
  refine (GlobalTheory.GoodTypeGeneric.sum_character_eq_zero_iff ρu).2 ?_
  intro v hv
  obtain ⟨i0, j0, h0⟩ : ∃ i0 j0, c' i0 < c' j0 := by
    obtain ⟨i, j, hij⟩ := hc'
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  let F := Fintype.equivFin {i // b i = c}
  let bb : {i // b i = c} → Fin 2 := fun x => if c' (F x) ≤ c' i0 then 0 else 1
  have hbb : Function.Surjective bb := by
    intro k
    fin_cases k
    · exact ⟨F.symm i0, by simp [bb]⟩
    · exact ⟨F.symm j0, by simp [bb, not_le.2 h0]⟩
  refine hτ 2 bb hbb le_rfl v fun u hu => ?_
  set u' := (blockGL b c).symm u with hu'def
  have hu'u : blockGL b c u' = u := MulEquiv.apply_symm_apply _ _
  have hent : ∀ k l, (u' : Matrix _ _ K) k l = (u : Matrix _ _ K) (F.symm k) (F.symm l) := by
    intro k l
    rw [← hu'u, blockGL_apply]
    simp [F]
  have hmem : u' ∈ GlobalTheory.FiniteGL.unipRadical K c' := by
    rw [GlobalTheory.FiniteGL.mem_unipRadical]
    intro k l hlk
    rw [Matrix.sub_apply, hent]
    have hb : ∀ m, bb (F.symm m) = if c' m ≤ c' i0 then 0 else 1 := fun m => by simp [bb]
    by_cases hkl : bb (F.symm k) = bb (F.symm l)
    · rw [hu.2 _ _ hkl]
      by_cases e : k = l
      · subst e; simp
      · rw [if_neg (fun h => e (F.symm.injective h)), Matrix.one_apply_ne e, sub_zero]
    · have hk : ¬ c' k ≤ c' i0 := fun hk => hkl (by rw [hb, hb, if_pos hk, if_pos (hlk.trans hk)])
      have hl : c' l ≤ c' i0 := by
        by_contra hl
        exact hkl (by rw [hb, hb, if_neg hk, if_neg hl])
      have hlt : bb (F.symm l) < bb (F.symm k) := by
        rw [hb, hb, if_neg hk, if_pos hl]; decide
      have ekl : k ≠ l := fun e => hkl (by rw [e])
      rw [hu.1.1 _ _ hlt, Matrix.one_apply_ne ekl, sub_zero]
  have := hv ⟨u', hmem⟩
  simpa [ρu, hu'u] using this

theorem isIrrChar_block (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K)) (hτ : Simple τ) :
    IsIrrChar ℂ ℂ (fun g : GL (Fin (Fintype.card {i // b i = c})) K => LinearMap.trace ℂ τ (τ.ρ (blockGL b c g))) := by
  have hi := GlobalTheory.FinGL.Transport.isIrreducible_comp τ.ρ (blockGL b c).toMonoidHom (blockGL b c).surjective
    (GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ hτ)
  have h := (isChar_and_isIrrChar_of_rep ℂ ℂ _ τ (τ.ρ.comp (blockGL b c).toMonoidHom)).2 hi
  simpa [Representation.character] using h

theorem isCuspProdChar_trace_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → Monotone b →
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x)) := by
  intro K _ _ _ r s b lam _ hlam hmono
  classical
  let b₀ : Fin r → ℕ := fun i => (b i : ℕ)
  have hb₀ : Monotone b₀ := fun i j h => hmono h
  let d : Fin s → ℕ := fun c => Fintype.card {i // b i = c}
  let e : (Σ c, Fin (d c)) ≃ Fin r :=
    (Equiv.sigmaCongrRight fun c => (Fintype.equivFin {i // b i = c}).symm).trans (Equiv.sigmaFiberEquiv b)
  have hbe : ∀ x, b (e x) = x.1 := fun x => ((Fintype.equivFin {i // b i = x.1}).symm x.2).2
  have he : ∀ x y, b₀ (e x) = b₀ (e y) ↔ x.1 = y.1 := by
    intro x y
    simp only [b₀, hbe, Fin.val_inj]
  let χ : ∀ c, GL (Fin (d c)) K → ℂ := fun c g => LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c g))
  obtain ⟨n, σ, hσ, hch⟩ := GlobalTheory.GoodTypeGeneric.exists_isCuspDatum (F := K) hb₀ e he χ
    (fun c => isIrrChar_block b c (lam c) (hlam c).1)
    (fun c c' hc' => sum_unipRadical_eq_zero b c (lam c) (hlam c).2 c' hc')
  refine ⟨n, b₀, σ, hσ, fun x => ?_⟩
  have hPB := parab_eq_blockTri (K := K) b
  let f : blockTri (κ := K) b₀ →* parab K b :=
    MonoidHom.codRestrict (blockTri (κ := K) b₀).subtype (parab K b) (fun p => by rw [hPB]; exact p.2)
  have hf : Function.Surjective f := fun p => ⟨⟨p.1, by rw [← hPB]; exact p.2⟩, rfl⟩
  have h1 : LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) =
      (Representation.coind (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam)).character x := rfl
  show LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) = _
  have h2 := GlobalTheory.FinGL.Transport.character_coind (parab K b).subtype (blockTri (κ := K) b₀).subtype
    (PI.SerBridgeGLW.inflRep K b lam) (MulEquiv.refl _) f hf (fun _ => rfl) x
  rw [MulEquiv.refl_apply] at h2
  rw [h1, ← h2]
  rw [GlobalTheory.GoodTypeGeneric.character_coind_eq_ind, GlobalTheory.GoodTypeGeneric.character_coind_eq_ind]
  congr 1
  funext p
  rw [hch p]
  show LinearMap.trace ℂ _ (PiTensorProduct.map fun c => (lam c).ρ (levi K b c (f p))) = _
  rw [PI.SerBridgeGLW.trace_piTensorMap]
  refine Finset.prod_congr rfl fun c _ => ?_
  show _ = LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c _))
  congr 3
  apply Units.ext
  ext x y
  rw [blockGL_apply, GlobalTheory.GoodTypeGeneric.blocksHom_apply]
  have hx : ∀ z : {i // b i = c}, e ⟨c, Fintype.equivFin _ z⟩ = z.1 := fun z => by
    simp [e, Equiv.sigmaFiberEquiv]
  rw [hx, hx]
  rfl

end GlobalTheory.HCInduction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorConstantTermSum
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.HeckeCT

open Formalism.UG Formalism.UG.P GlobalTheory.LFun

section Tri

variable {R T : Type} [CommRing R] [CommRing T] {r s N : ℕ} (h : r + s = N)

def Tri (g : GL (Fin N) R) (m : GL (Fin r) R × GL (Fin s) R) : Prop :=
  ∃ X, g.val.submatrix (blkE h) (blkE h) = Matrix.fromBlocks m.1.val X 0 m.2.val

theorem blk_sub (m : GL (Fin r) R × GL (Fin s) R) :
    (blk h m).val.submatrix (blkE h) (blkE h) = Matrix.fromBlocks m.1.val 0 0 m.2.val := by
  change (Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks m.1.val 0 0 m.2.val)).submatrix _ _ = _
  simp

theorem tri_blk (m : GL (Fin r) R × GL (Fin s) R) : Tri h (blk h m) m := ⟨0, blk_sub h m⟩

variable {h}

theorem Tri.mul {g g' : GL (Fin N) R} {m m' : GL (Fin r) R × GL (Fin s) R} (a : Tri h g m) (b : Tri h g' m') :
    Tri h (g * g') (m * m') := by
  obtain ⟨X, a⟩ := a
  obtain ⟨Y, b⟩ := b
  refine ⟨m.1.val * Y + X * m'.2.val, ?_⟩
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ (blkE h), a, b, Matrix.fromBlocks_multiply]
  simp

end Tri

theorem blk_mem {L : Type} [Field L] {O : Subring L} {r s N : ℕ} (h : r + s = N) {m : GL (Fin r) L × GL (Fin s) L}
    (h1 : m.1 ∈ GLint (Fin r) O) (h2 : m.2 ∈ GLint (Fin s) O) : blk h m ∈ GLint (Fin N) O := by
  have key : ∀ m : GL (Fin r) L × GL (Fin s) L, m.1 ∈ GLint (Fin r) O → m.2 ∈ GLint (Fin s) O →
      ∀ a b, (blk h m).val a b ∈ O := fun m h1 h2 a b => by
    obtain ⟨a, rfl⟩ := (blkE h).surjective a
    obtain ⟨b, rfl⟩ := (blkE h).surjective b
    have := congrFun (congrFun (blk_sub h m) a) b
    rw [Matrix.submatrix_apply] at this
    rw [this]
    rcases a with a | a <;> rcases b with b | b
    exacts [satake_glint_entry O h1 a b, O.zero_mem, O.zero_mem, satake_glint_entry O h2 a b]
  refine satake_mem_glint O _ (key m h1 h2) ?_
  rw [← map_inv]
  exact key _ (inv_mem h1) (inv_mem h2)

theorem sum_fun {α A B C Q : Type} [Fintype α] [Fintype A] [Fintype B] [Fintype C] [Fintype Q] [DecidableEq α]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (e : A ⊕ B ⊕ C ≃ α) (G : (A → Q) → (B → Q) → ℂ) :
    ∑ c : α → Q, G (fun a => c (e (.inl a))) (fun b => c (e (.inr (.inl b)))) =
      (Fintype.card Q : ℂ) ^ Fintype.card C * ∑ a, ∑ b, G a b := by
  let f : (A → Q) × (B → Q) × (C → Q) ≃ (α → Q) :=
    (((Equiv.sumArrowEquivProdArrow _ _ _).trans
      ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ _))).symm).trans (e.arrowCongr (Equiv.refl Q))
  rw [← f.sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [f]

section Pairs

variable {r s N : ℕ} (h : r + s = N) {S : Finset (Fin N)} {S₁ : Finset (Fin r)} {S₂ : Finset (Fin s)}
  (h1 : ∀ a, blkE h (.inl a) ∈ S ↔ a ∈ S₁) (h2 : ∀ a, blkE h (.inr a) ∈ S ↔ a ∈ S₂)

def pairMap : satakePairs S₁ ⊕ satakePairs S₂ ⊕ (S₁ × (S₂ᶜ : Finset (Fin s))) → satakePairs S
  | .inl p => ⟨(blkE h (.inl p.1.1), blkE h (.inl p.1.2)), (h1 _).2 p.2.1, fun e => p.2.2.1 ((h1 _).1 e), p.2.2.2⟩
  | .inr (.inl p) => ⟨(blkE h (.inr p.1.1), blkE h (.inr p.1.2)), (h2 _).2 p.2.1, fun e => p.2.2.1 ((h2 _).1 e),
      Nat.add_lt_add_left p.2.2.2 r⟩
  | .inr (.inr p) => ⟨(blkE h (.inl p.1.1), blkE h (.inr p.2.1)), (h1 _).2 p.1.2,
      fun e => Finset.mem_compl.1 p.2.2 ((h2 _).1 e), Nat.lt_add_right _ p.1.1.2⟩

theorem pairMap_bijective : Function.Bijective (pairMap h h1 h2) := by
  constructor
  · rintro (p | p | p) (p' | p' | p') e <;> simp [pairMap] at e ⊢
    · exact Subtype.ext (Prod.ext e.1 e.2)
    · exact Subtype.ext (Prod.ext e.1 e.2)
    · exact Prod.ext e.1 e.2
  · rintro ⟨⟨a, b⟩, x, y, z⟩
    obtain ⟨a, rfl⟩ := (blkE h).surjective a
    obtain ⟨b, rfl⟩ := (blkE h).surjective b
    rcases a with a | a <;> rcases b with b | b
    · exact ⟨.inl ⟨(a, b), (h1 _).1 x, fun e => y ((h1 _).2 e), z⟩, rfl⟩
    · exact ⟨.inr (.inr (⟨a, (h1 _).1 x⟩, ⟨b, Finset.mem_compl.2 fun e => y ((h2 _).2 e)⟩)), rfl⟩
    · exact absurd (Nat.lt_add_right a b.2) (not_lt.2 (le_of_lt z))
    · exact ⟨.inr (.inl ⟨(a, b), (h2 _).1 x, fun e => y ((h2 _).2 e), Nat.lt_of_add_lt_add_left z⟩), rfl⟩

theorem tri_satakeGL {L : Type} [Field L] (O : Subring L) {π : L} (hπ : π ≠ 0) (c : satakePairs S → O) :
    Tri h (satakeGL O hπ S c) (satakeGL O hπ S₁ fun p => c (pairMap h h1 h2 (.inl p)),
      satakeGL O hπ S₂ fun p => c (pairMap h h1 h2 (.inr (.inl p)))) := by
  refine ⟨Matrix.of fun a b => (satakeGL O hπ S c).val (blkE h (.inl a)) (blkE h (.inr b)), ?_⟩
  ext (a | a) (b | b)
  · have : blkE h (.inl a) < blkE h (.inl b) ↔ a < b := Iff.rfl
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, satakeGL_apply, satakeN, h1, this, Matrix.one_apply,
      Equiv.apply_eq_iff_eq, Sum.inl.injEq]
    rfl
  · rfl
  · exact satakeGL_lower O hπ S c _ _ (Nat.lt_add_right a b.2)
  · have : blkE h (.inr a) < blkE h (.inr b) ↔ a < b := Nat.add_lt_add_iff_left
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, satakeGL_apply, satakeN, h2, this, Matrix.one_apply,
      Equiv.apply_eq_iff_eq, Sum.inr.injEq]
    rfl

end Pairs

section Local

variable {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {ϖ : v.adicCompletion E}
  (hu : IsUnifV E v ϖ)

abbrev Res : Type := satakeRes (Ov E v) ⟨ϖ, mem_Ov_of_isUnifV hu⟩

abbrev rep {n : ℕ} (S : Finset (Fin n)) (c : satakePairs S → Res hu) : GL (Fin n) (v.adicCompletion E) :=
  satakeGL (Ov E v) (satake_unif_ne_zero v hu) S fun p => satakeSec (Ov E v) ⟨ϖ, mem_Ov_of_isUnifV hu⟩ (c p)

variable [Fintype (Res hu)]

theorem finsum_Tj {n j : ℕ} (hj : j ≤ n) (F : GL (Fin n) (v.adicCompletion E) → ℂ)
    (hF : ∀ g, ∀ k ∈ KGL v n, F (g * k) = F g) :
    ∑ᶠ c : GL (Fin n) (v.adicCompletion E) ⧸ KGL v n, Tj ℂ n (Ov E v) ϖ j c.out * F c.out =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, ∑ c : satakePairs S → Res hu, F (rep hu S c) := by
  classical
  have hϖ := mem_Ov_of_isUnifV hu
  have hr := satake_range_eq v hϖ hu Final.TjCosets hj
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion E)) : GL (Fin n) (v.adicCompletion E) ⧸ KGL v n))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj v hϖ hu h),
      Finset.sum_subtype (Finset.univ.powersetCard j) (p := fun S : Finset (Fin n) => S.card = j)
        (fun S => by simp [Finset.mem_powersetCard]), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (KGL v n) (satakeB v hϖ hu ⟨S, c⟩)
    rw [hκ, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right v (satakeB_mem v hϖ hu ⟨S, c⟩) κ.2),
      Pi.one_apply, one_mul, hF _ _ κ.2]
    rfl
  · intro x hx
    have hT : Tj ℂ n (Ov E v) ϖ j x.out ≠ 0 := left_ne_zero_of_mul hx
    rw [satake_Tj_ne_zero_iff] at hT
    obtain ⟨i, rfl⟩ := (Set.ext_iff.1 hr x).2 hT
    simp

theorem sum_rep {r s N : ℕ} (h : r + s = N) {S : Finset (Fin N)} {S₁ : Finset (Fin r)} {S₂ : Finset (Fin s)}
    (h1 : ∀ a, blkE h (.inl a) ∈ S ↔ a ∈ S₁) (h2 : ∀ a, blkE h (.inr a) ∈ S ↔ a ∈ S₂)
    (F : GL (Fin N) (v.adicCompletion E) → ℂ) (hF : ∀ g m, Tri h g m → F g = F (blk h m)) :
    ∑ c : satakePairs S → Res hu, F (rep hu S c) = (qV E v : ℂ) ^ (S₁.card * (s - S₂.card)) *
      ∑ c₁ : satakePairs S₁ → Res hu, ∑ c₂ : satakePairs S₂ → Res hu, F (blk h (rep hu S₁ c₁, rep hu S₂ c₂)) := by
  have := sum_fun (Equiv.ofBijective _ (pairMap_bijective h h1 h2))
    fun (c₁ : satakePairs S₁ → Res hu) (c₂ : satakePairs S₂ → Res hu) => F (blk h (rep hu S₁ c₁, rep hu S₂ c₂))
  rw [← Nat.card_eq_fintype_card, satake_card_res v _ hu, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_compl, Fintype.card_fin] at this
  rw [← this]
  exact Finset.sum_congr rfl fun c _ => hF _ _ (tri_satakeGL h h1 h2 _ _ _)

omit [Fintype (Res hu)] in
include hu in

theorem finsum_Tj_levi {r s N j : ℕ} (h : r + s = N) (hj : j ≤ N) (F : GL (Fin N) (v.adicCompletion E) → ℂ)
    (hK : ∀ g, ∀ k ∈ KGL v N, F (g * k) = F g) (hF : ∀ g m, Tri h g m → F g = F (blk h m)) :
    ∑ᶠ c : GL (Fin N) (v.adicCompletion E) ⧸ KGL v N, Tj ℂ N (Ov E v) ϖ j c.out * F c.out =
      ∑ i ∈ (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j),
        (qV E v : ℂ) ^ (i.1 * (s - i.2)) * ∑ᶠ c₁ : GL (Fin r) (v.adicCompletion E) ⧸ KGL v r,
          ∑ᶠ c₂ : GL (Fin s) (v.adicCompletion E) ⧸ KGL v s,
            Tj ℂ r (Ov E v) ϖ i.1 c₁.out * Tj ℂ s (Ov E v) ϖ i.2 c₂.out * F (blk h (c₁.out, c₂.out)) := by
  classical
  have := satake_res_finite v (mem_Ov_of_isUnifV hu) hu
  let _ : Fintype (Res hu) := Fintype.ofFinite _
  let J : Finset (Fin r) × Finset (Fin s) ≃ Finset (Fin N) :=
    Finset.sumEquiv.symm.toEquiv.trans (blkE h).finsetCongr
  have hJ : ∀ T, J T = (T.1.disjSum T.2).map (blkE h).toEmbedding := fun _ => rfl
  rw [finsum_Tj hu hj F hK,
    ← Finset.sum_equiv J (s := Finset.univ.filter fun T => T.1.card + T.2.card = j)
      (f := fun T => ∑ c : satakePairs (J T) → Res hu, F (rep hu (J T) c))
      (fun T => by simp [hJ, Finset.mem_powersetCard]) (fun _ _ => rfl),
    ← Finset.sum_fiberwise_of_maps_to (g := fun T : Finset (Fin r) × Finset (Fin s) => (T.1.card, T.2.card))
      (t := (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j)) (fun T hT => by
        have a1 := Finset.card_le_univ T.1
        have a2 := Finset.card_le_univ T.2
        simp only [Fintype.card_fin] at a1 a2
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hT ⊢
        omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hi
  have e1 : ∀ g : GL (Fin r) (v.adicCompletion E), ∑ᶠ c₂ : GL (Fin s) (v.adicCompletion E) ⧸ KGL v s,
      Tj ℂ r (Ov E v) ϖ i.1 g * Tj ℂ s (Ov E v) ϖ i.2 c₂.out * F (blk h (g, c₂.out)) =
      Tj ℂ r (Ov E v) ϖ i.1 g * ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard i.2,
        ∑ c : satakePairs S → Res hu, F (blk h (g, rep hu S c)) := fun g => by
    rw [← finsum_Tj hu hi.1.2 (fun x => F (blk h (g, x))) fun x k hk => ?_, mul_finsum]
    · simp only [mul_assoc]
    · rw [← hK (blk h (g, x)) _ (blk_mem h (m := (1, k)) (one_mem _) hk), ← map_mul]
      simp
  simp only [e1]
  rw [finsum_Tj hu hi.1.1 (fun g => ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard i.2,
        ∑ c : satakePairs S → Res hu, F (blk h (g, rep hu S c))) fun x k hk =>
      Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun c _ => by
        rw [← hK (blk h (x, _)) _ (blk_mem h (m := (k, 1)) hk (one_mem _)), ← map_mul]
        simp]
  rw [Finset.sum_congr (s₂ := Finset.univ.powersetCard i.1 ×ˢ Finset.univ.powersetCard i.2) ?_ fun _ _ => rfl,
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun S₁ hS₁ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    rw [sum_rep hu h (S₁ := S₁) (S₂ := S₂) (fun a => by simp [hJ]) (fun a => by simp [hJ]) F hF,
      (Finset.mem_powersetCard.1 hS₁).2, (Finset.mem_powersetCard.1 hS₂).2]
  · ext T
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ, Prod.ext_iff]
    omega

end Local

section Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

end Global

end GlobalTheory.ResW.HeckeCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormSignatureRealisation
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.UnitaryClasses

theorem gramOn_map_eq_H {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).map τ =
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ)ᴴ * H.map τ *
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k)) := by
  ext i j
  simp [gramOn, hform, Matrix.mul_apply, Matrix.conjTranspose_apply,
    IsCMField.complexEmbedding_complexConj, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem gramOn_det_totallyPositive_of_posDef {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E)
    (hH : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q)
    (V : Submodule E (Fin n → E)) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det ≠ 0 ∧
      ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det = r := by
  have key : ∀ τ : E →+* ℂ, 0 < τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det := by
    intro τ
    obtain ⟨Q, hQ, hHQ⟩ := hH τ
    rw [RingHom.map_det]
    have e1 : τ.mapMatrix (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V) =
        (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).map τ := rfl
    have e2 : cT (starRingEnd ℂ) Q = Qᴴ := by
      ext i j; simp [cT, Matrix.conjTranspose_apply]
    set A : Matrix (Fin n) (Fin (Module.finrank E V)) ℂ :=
      Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) with hA
    have e3 : Aᴴ * (Qᴴ * Q) * A = (Q * A)ᴴ * (Q * A) := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, gramOn_map_eq_H, ← hA, hHQ, e2, e3]
    have hQi : Function.Injective Q.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hQ
    have hinj : Function.Injective (Q * A).mulVec := by
      intro v w hvw
      simp only [← Matrix.mulVec_mulVec] at hvw
      exact gramOn_basis_mulVec_injective V τ (hQi hvw)
    exact (Matrix.PosDef.conjTranspose_mul_self _ hinj).det_pos
  refine ⟨fun h0 => ?_, fun τ => ?_⟩
  · have τ0 := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
    have := key τ0
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  · have h := Complex.lt_def.mp (key τ)
    refine ⟨(τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det).re, h.1, ?_⟩
    apply Complex.ext
    · simp
    · simpa using h.2.symm

theorem refSign_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) := by
  intro E _ _ _ hU S hS n γ₀ _ H₀ _ _ _ hpos P₁ _ _
  obtain ⟨hd0, hdpos⟩ := gramOn_det_totallyPositive_of_posDef H₀ hpos
    (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))
  refine Eq.trans ?_ (GlobalTheory.T.finprod_nonsplit_sign_totallyPositive_eq_one E hU S hS _ hd0 hdpos)
  apply finprod_mem_congr rfl
  intro w _
  split_ifs with hw
  · rfl
  · unfold sgnOn
    rw [aeval_map_mat]
    exact GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq E hU w hw n H₀ (aeval γ₀.val P₁)

end GlobalTheory.UnitaryClasses
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairLatticeLocalSplit
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.IwSplitLine

theorem iwasawa_line_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * y = 0 → cT (σ : E →+* E) x * J * y = 1 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ h n J hJ x y hxx hyy hxy hyx L hLat v hv hL g
  obtain ⟨P, P', hne, hP, hP'⟩ := hv
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq h (v := v) hne (IsDedekindDomain.HeightOneSpectrum.ext hP) (IsDedekindDomain.HeightOneSpectrum.ext hP')
  obtain ⟨k, i, qq, hn, hsum⟩ := GlobalTheory.IwSplitFrame.exists_compl x y (cT (σ : E →+* E) y * J) (cT (σ : E →+* E) x * J)
    hyx hyy hxx hxy
  obtain ⟨B, lv, hB⟩ := GlobalTheory.Core.Rk.IwFlagSplit.exists_flag_basis (v := v) τ hJ
    (e := x) (e' := y) (i := i) (p := cT (σ : E →+* E) y * J) (q := qq)
    (Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)) hsum hxy
  have hQ : ∀ z : GLoc σ J v, (B⁻¹ * splitHom σ J τ z * B).1.BlockTriangular lv →
      z ∈ GlobalTheory.IwSplitFrame.keepGrp (σ := σ) (J := J) (v := v) (x.map (inclR (F := F) (Fv F v))) :=
    fun z hz => by
      obtain ⟨⟨b, hb⟩, b', hb'⟩ := hB z hz
      exact GlobalTheory.IwSplitFrame.keeps_of_split h τ z hyx hb hb'
  obtain ⟨q, k', hq, hk, rfl⟩ := GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_of_triangular h hJ τ L hL _ B lv hQ g
  obtain ⟨β, hβ⟩ := hq
  exact ⟨q, k', hk, rfl, β, hβ⟩

end GlobalTheory.IwSplitLine
end
end

