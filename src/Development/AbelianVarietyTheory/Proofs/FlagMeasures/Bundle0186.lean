import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0172
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryHermFrameUnipotent

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLatticeQuotPrime
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

noncomputable section

namespace GlobalTheory.AdelicLattice

theorem card_quot_smul_top_of_flat {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Flat R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
    Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

def inclLat (I : AutInst) : I.L →+ I.Lf where
  toFun x := ⟨fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x.1 i), incl_mem_lamAf I.L x.2⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' x y := Subtype.ext (funext fun i => map_add _ (x.1 i) (y.1 i))

theorem inclLat_smul (I : AutInst) (a : 𝓞 I.E) (x : I.L) :
    inclLat I (a • x) = Inhab.psi I.F I.E a • inclLat I x :=
  Subtype.ext (funext fun i => map_mul (Formalism.UG.inclE (F := I.F) (Af I.F)) (a : I.E) (x.1 i))

theorem exists_inclLat_add (I : AutInst) {p : ℕ} (hp : p ≠ 0) (y : I.Lf) :
    ∃ (x : I.L) (z : I.Lf), y = inclLat I x + (p : IntAf I.F I.E) • z := by
  obtain ⟨x, hx, z, hz, e⟩ := exists_approx I.L p (Nat.one_le_iff_ne_zero.2 hp) y.1 y.2
  refine ⟨⟨x, hx⟩, ⟨z, hz⟩, Subtype.ext ?_⟩
  rw [e]
  funext i
  show _ + (p : I.E ⊗[I.F] Af I.F) * z i = _ + ((p : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) * z i
  rw [Subring.coe_natCast]
  rfl

theorem exists_eq_smul_of_inclLat (I : AutInst) {p : ℕ} (hp : p ≠ 0) (x : I.L) (z : I.Lf)
    (h : inclLat I x = (p : IntAf I.F I.E) • z) : ∃ u : I.L, x = (p : 𝓞 I.E) • u := by
  have hpE : (p : I.E) ≠ 0 := by exact_mod_cast hp
  have hz : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((p : I.E)⁻¹ • x.1) i)) = z.1 := by
    funext i
    have hi : Formalism.UG.inclE (F := I.F) (Af I.F) (x.1 i) =
        ((p : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) * z.1 i := congrFun (congrArg Subtype.val h) i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hi, Subring.coe_natCast,
      ← map_natCast (Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)) p, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hpE, map_one, one_mul]
  refine ⟨⟨_, (incl_mem_iff (F := I.F) I.L I.L_fg I.L_span ((p : I.E)⁻¹ • x.1)).1 (hz ▸ z.2)⟩,
    Subtype.ext (funext fun i => ?_)⟩
  show x.1 i = algebraMap (𝓞 I.E) I.E (p : 𝓞 I.E) * ((p : I.E)⁻¹ * x.1 i)
  rw [map_natCast, mul_inv_cancel_left₀ hpE]

theorem card_quot_eq_of_dense {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (ψ : R →+* S) (ι : M →+ N) (hι : ∀ a x, ι (a • x) = ψ a • ι x) (p : ℕ)
    (𝔞 : Ideal R) (𝔟 : Ideal S) (hpa : (p : R) ∈ 𝔞) (hab : ∀ a ∈ 𝔞, ψ a ∈ 𝔟)
    (hba : ∀ s ∈ 𝔟, ∃ a ∈ 𝔞, ∃ t : S, s = ψ a + (p : S) * t)
    (hd : ∀ y : N, ∃ (x : M) (z : N), y = ι x + (p : S) • z)
    (hi : ∀ (x : M) (z : N), ι x = (p : S) • z → ∃ u : M, x = (p : R) • u) :
    Nat.card (N ⧸ (𝔟 • ⊤ : Submodule S N)) = Nat.card (M ⧸ (𝔞 • ⊤ : Submodule R M)) := by
  have hpe : (p : S) ∈ 𝔟 := by simpa using hab _ hpa
  let φ : M →+ N ⧸ (𝔟 • ⊤ : Submodule S N) := (𝔟 • ⊤ : Submodule S N).mkQ.toAddMonoidHom.comp ι
  have hφ : ∀ x, φ x = Submodule.Quotient.mk (ι x) := fun _ => rfl
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, z, rfl⟩ := hd y
    refine ⟨x, ?_⟩
    rw [hφ, eq_comm, Submodule.Quotient.eq, add_sub_cancel_left]
    exact Submodule.smul_mem_smul hpe Submodule.mem_top
  have hdec : ∀ y ∈ (𝔟 • ⊤ : Submodule S N), ∃ x ∈ (𝔞 • ⊤ : Submodule R M), ∃ z : N,
      y = ι x + (p : S) • z := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
    · obtain ⟨b, hb, t, e⟩ := hba a ha
      obtain ⟨x, z, rfl⟩ := hd y
      refine ⟨b • x, Submodule.smul_mem_smul hb Submodule.mem_top, t • ι x + a • z, ?_⟩
      rw [hι, smul_add, smul_add, smul_comm a, ← add_assoc, smul_smul _ t, ← add_smul, ← e]
    · obtain ⟨x, hx, z, rfl⟩ := hy
      obtain ⟨x', hx', z', rfl⟩ := hy'
      refine ⟨x + x', add_mem hx hx', z + z', ?_⟩
      rw [map_add, smul_add]
      abel
  have hker : (𝔞 • ⊤ : Submodule R M).toAddSubgroup = φ.ker := by
    refine AddSubgroup.ext fun x => ?_
    rw [AddMonoidHom.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_toAddSubgroup]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · refine Submodule.smul_induction_on h (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
      · rw [hι]
        exact Submodule.smul_mem_smul (hab a ha) Submodule.mem_top
      · rw [map_add]
        exact add_mem hy hy'
    · obtain ⟨x', hx', z, e⟩ := hdec _ h
      obtain ⟨u, hu⟩ := hi (x - x') z (by rw [map_sub, e, add_sub_cancel_left])
      rw [← sub_add_cancel x x', hu]
      exact add_mem (Submodule.smul_mem_smul hpa Submodule.mem_top) hx'
  have e : (M ⧸ (𝔞 • ⊤ : Submodule R M).toAddSubgroup) ≃ (N ⧸ (𝔟 • ⊤ : Submodule S N)) :=
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)).toEquiv
  exact (Nat.card_congr e).symm

theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

theorem finrank_lattice (I : AutInst) : Module.finrank (𝓞 I.E) I.L = I.n := by
  rw [finrank_of_span_top I.L I.L_span, Module.finrank_fin_fun]

theorem card_quot_extId : ∀ (I : AutInst) (p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)), p.Prime → Ideal.absNorm w.asIdeal = p → Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf))) = p ^ I.n := by
  intro I p w hp hw
  obtain ⟨r, hr⟩ := Inhab.exists_reduction (F := I.F) p hp w hw
  have hk := Inhab.ker_eq_extId hp.ne_zero r hr
  have hpw : (p : 𝓞 I.E) ∈ w.asIdeal := (hr _).1 (by rw [map_natCast, map_natCast, ZMod.natCast_self])
  have hab : ∀ a ∈ w.asIdeal, Inhab.psi I.F I.E a ∈ extId I w.asIdeal :=
    fun a ha => Ideal.subset_span ⟨a, ha, rfl⟩
  have hba : ∀ s ∈ extId I w.asIdeal, ∃ a ∈ w.asIdeal, ∃ t : IntAf I.F I.E,
      s = Inhab.psi I.F I.E a + (p : IntAf I.F I.E) * t := by
    intro s hs
    obtain ⟨b, t, e⟩ := Inhab.exists_approx hp.ne_zero s
    refine ⟨b, (hr b).1 ?_, t, e⟩
    have h0 : r s = 0 := (RingHom.mem_ker).1 (hk.ge hs)
    rw [e, r.map_add, r.map_mul, map_natCast r p, ZMod.natCast_self, zero_mul, add_zero] at h0
    exact h0
  refine (card_quot_eq_of_dense (Inhab.psi I.F I.E) (inclLat I) (inclLat_smul I) p w.asIdeal
    (extId I w.asIdeal) hpw hab hba (exists_inclLat_add I hp.ne_zero)
    (exists_eq_smul_of_inclLat I hp.ne_zero)).trans ?_
  have hfin : Finite (𝓞 I.E ⧸ w.asIdeal) := (Ideal.absNorm_ne_zero_iff _).1 (by rw [hw]; exact hp.ne_zero)
  have : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.2 I.L_fg
  have h := card_quot_smul_top_of_flat (N := I.L) w.asIdeal
  rw [finrank_lattice, ← Submodule.cardQuot_apply w.asIdeal, ← Ideal.absNorm_apply, hw] at h
  exact h

end GlobalTheory.AdelicLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellPointBlockEndsLeadingMinors
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.PtMinor

noncomputable def minor (bs : List (ℂ × ℕ)) (m : ℕ) : ℂ := (Matrix.of fun a b : Fin m => ptEntry bs a b).det

def ends (c : ℕ) (bs : List (ℂ × ℕ)) : List ℕ := ((bs.map Prod.snd).scanl (· + ·) c).tail

theorem ends_nil (c : ℕ) : ends c [] = [] := by simp [ends]

theorem ends_cons (c : ℕ) (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) :
    ends c ((t, s) :: bs) = (c + s) :: ends (c + s) bs := by
  cases bs <;> simp [ends]

theorem det_anti (t : ℂ) (ht : t ≠ 0) (s : ℕ) :
    (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det ≠ 0 := by
  have : (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0) =
      (Matrix.diagonal fun _ : Fin s => t).submatrix (Fin.revPerm : Equiv.Perm (Fin s)) id := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, Fin.revPerm_apply, id, Fin.ext_iff,
      Fin.val_rev]
    have := a.2
    exact if_congr (by omega) rfl rfl
  rw [this, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h | h <;> simp [h, ht]

theorem minor_cons (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) :
    minor ((t, s) :: bs) (s + m) =
      (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det * minor bs m := by
  unfold minor
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (0 : Matrix (Fin s) (Fin m) ℂ),
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [ptEntry]

theorem minor_lt (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) (h1 : 1 ≤ m) (h2 : m < s) :
    minor ((t, s) :: bs) m = 0 := by
  unfold minor
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h1⟩ fun j => ?_
  have := j.2
  simp only [Matrix.of_apply, ptEntry]
  split_ifs <;> first | rfl | omega

theorem ends_bd (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c : ℕ) :
    (∀ x ∈ ends c bs, c < x ∧ x ≤ c + (bs.map Prod.snd).sum) ∧ (ends c bs).Nodup ∧
      (bs ≠ [] → c + (bs.map Prod.snd).sum ∈ ends c bs) := by
  induction bs generalizing c with
  | nil => simp [ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have hs : 1 ≤ s := (h (t, s) (by simp)).2
    obtain ⟨i1, i2, i3⟩ := ih (fun b hb => h b (by simp [hb])) (c + s)
    rw [ends_cons]
    simp only [List.map_cons, List.sum_cons, List.mem_cons, List.nodup_cons]
    refine ⟨?_, ⟨fun hm => ?_, i2⟩, fun _ => ?_⟩
    · rintro x (rfl | hx)
      · omega
      · have := i1 x hx
        omega
    · have := i1 _ hm
      omega
    · by_cases hb : bs = []
      · subst hb; simp
      · right
        rw [← add_assoc]
        exact i3 hb

theorem minor_ne_iff (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c l : ℕ) (hl : 1 ≤ l) :
    minor bs l ≠ 0 ↔ c + l ∈ ends c bs := by
  induction bs generalizing c l with
  | nil =>
    have : minor [] l = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨0, hl⟩ fun j => by simp [ptEntry]
    simp [this, ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    have h' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b hb => h b (by simp [hb])
    have hb := (ends_bd bs h' (c + s)).1
    rw [ends_cons, List.mem_cons]
    rcases lt_or_ge l s with hls | hls
    · rw [minor_lt t s bs l hl hls]
      refine ⟨fun h0 => absurd rfl h0, ?_⟩
      rintro (h1 | h1)
      · omega
      · have := hb _ h1
        omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hls
      rw [minor_cons, mul_ne_zero_iff, and_iff_right (det_anti t ht s)]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [minor]
      · rw [ih h' (c + s) m hm, add_assoc]
        refine ⟨Or.inr, ?_⟩
        rintro (h1 | h1)
        · omega
        · exact h1

theorem one_le_max_inv (x : ℝ) (hx : 0 < x) : 1 ≤ max x x⁻¹ := by
  rcases le_total 1 x with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hx).2 h)

theorem list_prod (L : List ℕ) (f : ℕ → ℝ) (hf : ∀ l ∈ L, 1 ≤ f l) (a a' : ℝ) (ha : 0 ≤ a) (ha' : a ≤ a') :
    1 ≤ (L.map fun l => f l ^ a).prod ∧ (L.map fun l => f l ^ a).prod ≤ (L.map fun l => f l ^ a').prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨i1, i2⟩ := ih fun l hl => hf l (by simp [hl])
    have hx : 1 ≤ f x := hf x (by simp)
    have h1 := Real.one_le_rpow hx ha
    have h2 := Real.rpow_le_rpow_of_exponent_le hx ha'
    simp only [List.map_cons, List.prod_cons]
    exact ⟨one_le_mul_of_one_le_of_one_le h1 i1, mul_le_mul h2 i2 (by linarith) (by linarith)⟩

theorem one_le_foldr (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons x L ih => exact le_max_of_le_right ih

theorem blockEnds_minors : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → RelPt D z z' γ p → (∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p)) ∧ (ptBlockEnds p).Nodup ∧ (∀ l ∈ ptBlockEnds p, 1 ≤ l ∧ l ≤ D.R.rS + 1) ∧ D.R.rS + 1 ∈ ptBlockEnds p ∧ DminN z z' γ 0 = 1 ∧ 0 < Gf D.R.k D.R.rS z z' γ ∧ Gf D.R.k D.R.rS z z' γ ≤ ‖DminN z z' γ (D.R.rS + 1)‖ ^ 2 ∧ ∀ b C C₂ : ℝ, 1 ≤ b → 0 ≤ C → C ≤ C₂ → 1 ≤ lossV b C D.R.m z z' γ p ∧ lossV b C D.R.m z z' γ p ≤ lossV b C₂ D.R.m z z' γ p ∧ 1 ≤ lossP b C D.R.m z z' γ p ∧ lossP b C D.R.m z z' γ p ≤ lossP b C₂ D.R.m z z' γ p := by
  intro D z z' γ p hz hz' hT hT' hRel
  obtain ⟨hU, ⟨L, U, hL, hU', hZ⟩, hG⟩ := hRel
  have hp := p.2.1
  have hsum := p.2.2
  obtain ⟨e1, e2, e3⟩ := ends_bd p.1 hp 0
  rw [zero_add, hsum] at e1 e3
  have key : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Complex.normSq (DminN z z' γ l) = Complex.normSq (minor p.1 l) := by
    intro l hl
    have h1 := Formalism.MainNotions.S.Bridge.normSq_leadMinor_ZhatO D.R.k D.R.rS z z' γ l hl
    rw [hZ, Formalism.MainNotions.S.Bridge.leadMinor_cell L (ptMat p) U hL hU' l hl] at h1
    rw [DminN, dif_pos (Nat.lt_succ_of_le hl)]
    exact h1.symm
  have hiff : ∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p) := by
    intro l hl
    by_cases hl' : l ≤ D.R.rS + 1
    · have h2 := minor_ne_iff p.1 hp 0 l hl
      rw [zero_add] at h2
      rw [Ne, ← Complex.normSq_eq_zero, key l hl', Complex.normSq_eq_zero]
      exact h2
    · rw [DminN, dif_neg (by omega)]
      exact ⟨fun h0 => absurd rfl h0, fun hm => absurd (e1 l hm).2 hl'⟩
  have hG0 : 0 < Gf D.R.k D.R.rS z z' γ :=
    lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS z z' hz hz' hT hT' γ hU) (Ne.symm hG)
  refine ⟨hiff, e2, fun l hl => e1 l hl, e3 fun h0 => ?_, ?_, hG0, ?_, fun b C C₂ hb hC hC2 => ?_⟩
  · rw [h0] at hsum
    simp at hsum
  · simp [DminN, Formalism.QuantumDeterminants.Dmin]
  · rw [DminN, dif_pos (by omega), ← Complex.normSq_eq_norm_sq]
    have := mul_nonneg (mul_pos hT hT').le
      (Complex.normSq_nonneg (Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' γ ⟨D.R.rS, by omega⟩))
    exact sub_le_self _ this
  · have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have ex : ∀ x : ℝ, 0 ≤ x → 0 ≤ C * x ∧ C * x ≤ C₂ * x := fun x hx =>
      ⟨mul_nonneg hC hx, mul_le_mul_of_nonneg_right hC2 hx⟩
    obtain ⟨p1, p2⟩ := list_prod (ptBlockEnds p) (fun l => max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹)
      (fun l hl => one_le_max_inv _ (norm_pos_iff.2 ((hiff l (e1 l hl).1).2 hl))) _ _ (ex _ hm).1 (ex _ hm).2
    have g := one_le_max_inv _ hG0
    have a1 := Real.one_le_rpow hb (ex _ (pow_nonneg hm 4)).1
    have a2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ (pow_nonneg hm 4)).2
    have g1 := Real.one_le_rpow g (ex _ (pow_nonneg hm 2)).1
    have g2 := Real.rpow_le_rpow_of_exponent_le g (ex _ (pow_nonneg hm 2)).2
    have c1 := Real.one_le_rpow hb (ex _ hm).1
    have c2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ hm).2
    have f := one_le_foldr ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹)
    have q1 := one_le_mul_of_one_le_of_one_le c1 f
    have q2 := mul_le_mul_of_nonneg_right c2 (zero_le_one.trans f)
    refine ⟨one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le a1 g1) p1, ?_,
      Real.one_le_rpow q1 (ex _ (pow_nonneg hr 3)).1, ?_⟩
    · exact mul_le_mul (mul_le_mul a2 g2 (by linarith) (by linarith)) p2 (by linarith)
        (mul_nonneg (by linarith) (by linarith))
    · exact (Real.rpow_le_rpow (by linarith) q2 (ex _ (pow_nonneg hr 3)).1).trans
        (Real.rpow_le_rpow_of_exponent_le (q1.trans q2) (ex _ (pow_nonneg hr 3)).2)

end GlobalTheory.Amp.PtMinor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagFlagAdaptedLatticeBasis
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem eq_top_of_map_lattice_mem {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {m : ℕ}
    (Λ : Submodule (𝓞 E) (Fin m → E)) (hΛ : Submodule.span E (Λ : Set (Fin m → E)) = ⊤)
    (W : Submodule ℂ (Fin m → ℂ)) (h : ∀ t ∈ Λ, (fun l => φ (t l)) ∈ W) : W = ⊤ := by

  have hall : ∀ x : Fin m → E, (fun l => φ (x l)) ∈ W := by
    intro x
    have hx : x ∈ Submodule.span E (Λ : Set (Fin m → E)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem t ht => exact h t ht
    | zero =>
      have e1 : (fun l => φ ((0 : Fin m → E) l)) = 0 := by
        funext l; simp
      rw [e1]; exact W.zero_mem
    | add x y _ _ hx hy =>
      have e1 : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + (fun l => φ (y l)) := by
        funext l; simp
      rw [e1]; exact W.add_mem hx hy
    | smul c x _ hx =>
      have e1 : (fun l => φ ((c • x) l)) = φ c • (fun l => φ (x l)) := by
        funext l; simp
      rw [e1]; exact W.smul_mem _ hx

  have key : ∀ l, (Pi.single l (1 : ℂ) : Fin m → ℂ) ∈ W := by
    intro l
    convert hall (Pi.single l 1) using 1
    funext l'
    by_cases hl : l' = l
    · subst hl; simp
    · simp [hl]
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ l, w l • (Pi.single l (1 : ℂ) : Fin m → ℂ) := by
    funext l'; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact W.sum_mem fun l _ => W.smul_mem _ (key l)

theorem spansFlag_flagAt : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ v, SpansFlag (fun i => (I.P v)⁻¹ * (T i).map (I.φ v)) (flagAt I S v) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hA v k y
  obtain ⟨-, -, hlat, -, -, -, -, hS⟩ := hA

  have himg : ∀ u : ∀ i, Fin (j i) → I.E,
      ((I.P v)⁻¹ *ᵥ fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, ((I.P v)⁻¹ * (T i).map (I.φ v)) *ᵥ (fun l => I.φ v (u i l)) := by
    intro u
    have e1 : (fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, (T i).map (I.φ v) *ᵥ (fun l => I.φ v (u i l)) := by
      funext l
      simp only [Finset.sum_apply, map_sum, RingHom.map_mulVec, Function.comp_def]
    rw [e1, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.mulVec_mulVec _ _ _
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨u, -, hk, rfl⟩ := (hS k z).1 hz
      refine ⟨fun i l => I.φ v (u i l), fun i hi => ?_, himg u⟩
      funext l
      simp [hk i hi]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', rfl⟩ := hy
      refine ⟨u + u', fun i hi => by simp [hu i hi, hu' i hi], ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_add _ _ _).symm
    | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨c • u, fun i hi => by simp [hu i hi], ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_smul _ _ _).symm
  · rintro ⟨u, hu, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hik : i.castSucc < k
    ·
      have htop := eq_top_of_map_lattice_mem (I.φ v) (Λ i) (hlat i).span_eq_top
        ((flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v)))) (by
          intro t ht
          rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
          let w : ∀ i', Fin (j i') → I.E := Pi.single i t
          have hw1 : ∀ i', w i' ∈ Λ i' := by
            intro i'
            by_cases h' : i' = i
            · subst h'; simpa [w] using ht
            · simp [w, Pi.single_eq_of_ne h']
          have hw2 : ∀ i' : Fin a, ¬ i'.castSucc < k → w i' = 0 := by
            intro i' hi'
            have h' : i' ≠ i := by rintro rfl; exact hi' hik
            simp [w, Pi.single_eq_of_ne h']
          have hz : (∑ i', T i' *ᵥ w i') ∈ S k := (hS k _).2 ⟨w, hw1, hw2, rfl⟩
          have hmem := Submodule.subset_span (R := ℂ) (Set.mem_image_of_mem
            (fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) hz)
          have hsum := himg w
          rw [hsum, Finset.sum_eq_single i] at hmem
          · simp [w] at hmem
            exact hmem
          · intro i' _ h'
            simp [w, Pi.single_eq_of_ne h']
            exact Matrix.mulVec_zero _
          · simp)
      have : u i ∈ (flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v))) := by
        rw [htop]; trivial
      simpa [Submodule.mem_comap, Matrix.mulVecLin_apply] using this
    · simp [hu i hik]

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualVectorsNormalFormMemSecondFlagStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualVectors_normalForm_mem_secondFlag : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r j : ℕ} (hj : j ≤ r) (e e' s : Fin r → V),
    (Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b))).det ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → b.val < j → H.B (e a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ b.val → H.B (e a) (s b) = if a = b then 1 else 0) →
    (∀ a b : Fin r, a.val < j → j ≤ b.val → H.B (e' a) (s b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (s a) (s b) = 0) →
    ∃ f : Fin r → V, (∀ a, j ≤ a.val → f a = s a) ∧
      (∀ a, a.val < j → f a ∈ Submodule.span K (e' '' {b | b.val < j})) ∧
      (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, H.B (f a) (f b) = 0) ∧
      (∀ a, a.val < j → e' a ∈ Submodule.span K (f '' {b | b.val < j})) := by
  first | exact @GlobalTheory.dual_vectors_in_second_flag | exact GlobalTheory.dual_vectors_in_second_flag | (intros; apply GlobalTheory.dual_vectors_in_second_flag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryHermFrameUnipotentStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_hermFrame_unipotent : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r : ℕ} (e f e' f' : Fin r → V) (z z' : V),
    (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (f a) (f b) = 0) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, H.B (e a) z = 0) → (∀ a, H.B (f a) z = 0) → H.B z z ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) → (∀ a b, H.B (f' a) (f' b) = 0) →
    (∀ a b, H.B (e' a) (f' b) = if a = b then 1 else 0) →
    (∀ a, H.B (e' a) z' = 0) → (∀ a, H.B (f' a) z' = 0) →
    (∀ a, e' a - e a ∈ Submodule.span K (e '' {b | b < a})) →
    z' - z ∈ Submodule.span K (Set.range e) →
    ∃ m : V ≃ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) ∧ (∀ a, m (e' a) = e a) ∧ (∀ a, m (f' a) = f a) ∧
      m z' = z ∧ (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) ∧
      (∀ a, m.symm (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m.symm y - y ∈ Submodule.span K (Set.range e)) := by
  first | exact @GlobalTheory.RatIsoFrame.exists_isometry_frame_unipotent | exact GlobalTheory.RatIsoFrame.exists_isometry_frame_unipotent | (intros; apply GlobalTheory.RatIsoFrame.exists_isometry_frame_unipotent <;> assumption)
end

