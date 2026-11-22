import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PresentationTangentCombination
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLine.GrMinor

open GlobalTheory.LineNorm

theorem exists_ne {L : Type} [Field L] {g J : ℕ} (h : Fin J → Fin g → L)
    (hh : ∀ c : Fin g → L, (∀ j, ∑ i, h j i * c i = 0) → c = 0) {m : ℕ} (a : Fin m → Fin g → L)
    (ha : LinearIndependent L a) {k : ℕ} (hk : k ≤ m) :
    ∃ σ : Fin k → Fin J, ∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s ≠ 0 := by
  let G : Matrix (Fin J) (Fin m) L := Matrix.of fun j l => ∑ t, h j t * a l t
  have hli : LinearIndependent L G.transpose := by
    have hker : LinearMap.ker (Matrix.mulVecLin (Matrix.of h)) = ⊥ :=
      LinearMap.ker_eq_bot'.mpr fun c hc => hh c fun j => congrFun hc j
    exact ha.map' _ hker
  obtain ⟨κ, u, b, -, hu0, hu1, hb, hbd, hc⟩ := GlobalTheory.LineNorm.Covol.exists_pivot (⊤ : ValuationSubring L) G hli
  refine ⟨κ ∘ Fin.castLE hk, ?_⟩
  rw [GlobalTheory.LineNorm.Covol.sum_prod_mul_minor (fun i => h ((κ ∘ Fin.castLE hk) i)) a hk, ← Matrix.det_transpose]
  change (G.submatrix (κ ∘ Fin.castLE hk) (Fin.castLE hk)).det ≠ 0
  rw [hc, GlobalTheory.LineNorm.Covol.det_eq u b hb hk]
  have hMt : (u.submatrix (κ ∘ Fin.castLE hk) (Fin.castLE hk)).BlockTriangular OrderDual.toDual :=
    fun i j hij => hu0 _ _ hij
  rw [Matrix.det_of_isLowerTriangular _ hMt]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun l _ => hbd _)
  simp [hu1]

theorem sep_of_span {R S : Type} [CommRing R] [Field S] (ψ : R →+* S) (p : ℕ) (hp : (p : S) ≠ 0) {g J : ℕ}
    (h : Fin J → Fin g → R) (N : ℕ) (hN : ∀ i, Pi.single i ((p : R) ^ N) ∈ Submodule.span R (Set.range h))
    (c : Fin g → S) (hc : ∀ j, ∑ i, ψ (h j i) * c i = 0) : c = 0 := by
  have key : ∀ v ∈ Submodule.span R (Set.range h), ∑ i, ψ (v i) * c i = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hc j
    | zero => simp
    | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
    | smul r x _ hx =>
      calc ∑ i, ψ ((r • x) i) * c i = ψ r * ∑ i, ψ (x i) * c i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by simp <;> ring
        _ = 0 := by rw [hx, mul_zero]
  funext i
  have h1 := key _ (hN i)
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)] at h1
  simpa [hp] using h1

theorem norm_eq_iSup {κ : Type} [Fintype κ] [Nonempty κ] {S : Type} [NormedField S] (f : κ → S) :
    ‖f‖ = ⨆ i, ‖f i‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg ?_).2 fun i => le_ciSup (f := fun i => ‖f i‖) (Finite.bddAbove_range _) i)
    (ciSup_le fun i => norm_le_pi_norm f i)
  exact (norm_nonneg (f (Classical.arbitrary κ))).trans (le_ciSup (f := fun i => ‖f i‖) (Finite.bddAbove_range _) _)

theorem map_minor {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {m g k : ℕ} (a : Fin m → Fin g → R)
    (hk : k ≤ m) (s : Fin k → Fin g) : ψ (minor a hk s) = minor (fun l i => ψ (a l i)) hk s := by
  unfold minor
  rw [RingHom.map_det]
  rfl

end GlobalTheory.HTLine.GrMinor

namespace GlobalTheory.HTLine.GrMinor

open GlobalTheory.LineNorm GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem comb_eq {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t x (u i)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ i, a i • tanOf (hu i))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ i, a i • tanOf (hu i))).left := (isComb_iff (fun i => tanOf (hu i)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨v, hv, e⟩ := h
  obtain ⟨v', hv', e'⟩ := h0
  have : v = v' := funext fun i => Over.OverMorphism.ext ((hv i).trans (hv' i).symm)
  rw [← e, ← e', this]

theorem comb_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber S) ⟶ t.G.left)}
    (he : ∀ i, IsTanAtG t x (e i)) {w : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j))
    (a : Fin m → Fin g → S) (ha : ∀ j, IsCombAtG t x e (a j) (w j)) (cf : Fin m → S)
    (v : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x w cf v ↔ IsCombAtG t x e (fun r => ∑ l, cf l * a l r) v := by
  have hW : ∀ j, tanOf (hw j) = ∑ r, a j r • tanOf (he r) := fun j => tan_ext ((comb_eq he _ _).1 (ha j))
  rw [comb_eq hw, comb_eq he]
  have : ∑ l, cf l • tanOf (hw l) = ∑ r, (∑ l, cf l * a l r) • tanOf (he r) := by
    simp only [hW, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [this]

theorem linIndep_of_ind {k : Type} [Field k] {x : Sp k ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber k) ⟶ t.G.left)}
    (he : ∀ i, IsTanAtG t x (e i)) {w : Fin m → (Sp (DualNumber k) ⟶ t.G.left)} (hw : Pull.Ind t x w)
    (a : Fin m → Fin g → k) (ha : ∀ j, IsCombAtG t x e (a j) (w j)) : LinearIndependent k a := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : ∀ r, ∑ l, c l * a l r = ∑ l, (0 : Fin m → k) l * a l r := fun r => by
    have := congrFun hc r
    simpa [Finset.sum_apply] using this
  have h1 : IsCombAtG t x w c (tv (∑ l, c l • tanOf (hw.1 l))).left := (comb_eq hw.1 _ _).2 rfl
  have h2 : IsCombAtG t x w 0 (tv (∑ l, c l • tanOf (hw.1 l))).left := by
    rw [comb_comb he hw.1 a ha] at h1 ⊢
    rw [show (fun r => ∑ l, c l * a l r) = (fun r => ∑ l, (0 : Fin m → k) l * a l r) from funext h0] at h1
    exact h1
  exact congrFun (hw.2 _ _ _ h1 h2)

theorem coords {R : Type} [CommRing R] {x : Sp R ⟶ X} {g : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)}
    (he : IsTanBasis t x e) {m : ℕ} {w : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j)) :
    ∃ a : Fin m → Fin g → R, ∀ j, IsCombAtG t x e (a j) (w j) := by
  have h1 : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have h := he.2 R (RingHom.id R)
  simp only [h1, h3, Category.id_comp] at h
  choose a ha using fun j => (h (w j) (hw j)).exists
  exact ⟨a, ha⟩

end GlobalTheory.HTLine.GrMinor

namespace GlobalTheory.HTLine.GrMinor

open GlobalTheory.LineNorm GlobalTheory.LieMet

theorem grNorm_eq_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : ℕ) (b : Bool) (g M : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin (M + 1) → Fin g → R), p.Prime → GlobalTheory.LineNorm.IsTanBasis t x e → Pres t x p b e h → ∀ (m : ℕ) (w : Fin m → (Sp (DualNumber R) ⟶ t.G.left)), (∀ j, IsTanAtG t x (w j)) → (∀ (k : Type) [Field k] (ψ : R →+* k), (p : k) ≠ 0 → Pull.Ind t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ w j)) → ∀ i : Fin m, ∃ (a a' : ℕ) (A : Fin a → R) (B : Fin a' → R), (p : R) ∈ (Ideal.span (Set.range A)).radical ∧ (p : R) ∈ (Ideal.span (Set.range B)).radical ∧ ∀ (C : SCF p) (φ : R →+* ↥(intO ↥C.S)), GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b) (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ w j) i * ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖ := by
  intro E _ _ _ H X t R _ x p b g M e h hp he hP m w hw hind i
  obtain ⟨a, ha⟩ := coords he hw
  obtain ⟨N, hN⟩ := hP.1
  let F : ∀ k, k ≤ m → (Fin k → Fin (M + 1)) → R := fun k hk σ =>
    ∑ s : Fin k → Fin g, (∏ l, h (σ l) (s l)) * minor a hk s
  have hrad : ∀ k (hk : k ≤ m),
      (p : R) ∈ (Ideal.span (Set.range fun j => F k hk ((Fintype.equivFin _).symm j))).radical := by
    intro k hk
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro (P : Ideal R) ⟨hle, hPr⟩
    by_contra hpP
    haveI := hPr
    have hp0 : ((p : ℕ) : P.ResidueField) ≠ 0 := by
      rw [← map_natCast (algebraMap R P.ResidueField)]
      exact fun h0 => hpP (Ideal.algebraMap_residueField_eq_zero.1 h0)
    have hI := hind P.ResidueField (algebraMap R P.ResidueField) hp0
    have he' : ∀ r, IsTanAtG t (spMap (algebraMap R P.ResidueField) ≫ x)
        (spMap (dualMap (algebraMap R P.ResidueField)) ≫ e r) := fun r => isTan_map _ rfl (he.1 r)
    have ha' := fun j => GlobalTheory.LatDRFree.comb_map t (algebraMap R P.ResidueField) (ha j)
    have hli := linIndep_of_ind he' hI _ ha'
    obtain ⟨σ, hσ⟩ := exists_ne (fun j r => algebraMap R P.ResidueField (h j r))
      (sep_of_span _ p hp0 h N hN) _ hli hk
    apply hσ
    have hmem : F k hk σ ∈ P := hle (Ideal.subset_span ⟨Fintype.equivFin _ σ, by simp⟩)
    calc _ = algebraMap R P.ResidueField (F k hk σ) := by
          simp only [F, map_sum, map_mul, map_prod, map_minor]
      _ = 0 := Ideal.algebraMap_residueField_eq_zero.2 hmem
  refine ⟨_, _, fun j => F (i + 1) (Nat.succ_le_of_lt i.2) ((Fintype.equivFin _).symm j),
    fun j => F i i.2.le ((Fintype.equivFin _).symm j), hrad _ _, hrad _ _, fun C φ => ?_⟩
  set ψ : R →+* ↥C.S := (intO ↥C.S).subtype.comp φ with hψ
  have hx : spMap ψ ≫ x = spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hp0 : ((p : ℕ) : ↥C.S) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have he' : ∀ r, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (spMap (dualMap ψ) ≫ e r) :=
    fun r => isTan_map ψ hx (he.1 r)
  have hw' : ∀ l, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (spMap (dualMap ψ) ≫ w l) :=
    fun l => isTan_map ψ hx (hw l)
  have ha' : ∀ l, IsCombAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (fun r => spMap (dualMap ψ) ≫ e r)
      (fun r => ψ (a l r)) (spMap (dualMap ψ) ≫ w l) := fun l => hx ▸ GlobalTheory.LatDRFree.comb_map t ψ (ha l)
  have hI := hind ↥C.S ψ hp0
  rw [hx] at hI
  have hli := linIndep_of_ind he' hI _ ha'
  have hsep := sep_of_span ψ p hp0 h N hN
  let Nf : Fin m → ℝ := fun l => grNorm t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x)
    (lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b) (fun j => spMap (dualMap ψ) ≫ w j) l
  have hset : ∀ l, Nf l = sInf {r | ∃ cf : Fin m → ↥C.S, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧
      (∀ j, ‖∑ i, ψ (h j i) * ∑ l', cf l' * ψ (a l' i)‖ ≤ 1) ∧ r = ‖cf l‖⁻¹} := by
    intro l
    simp only [Nf, grNorm]
    congr 1
    ext r
    refine exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => ?_
    constructor
    · rintro ⟨v, hv, hc⟩
      exact (hP.2 C φ _ v ((comb_comb he' hw' _ ha' cf v).1 hc)).1 hv
    · intro hn
      have hc := (comb_eq hw' cf _).2 rfl
      exact ⟨_, (hP.2 C φ _ _ ((comb_comb he' hw' _ ha' cf _).1 hc)).2 hn, hc⟩
  obtain ⟨-, hprod⟩ := GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor ↥C.S g (Fin (M + 1)) (fun j r => ψ (h j r))
    hsep m (fun l r => ψ (a l r)) hli Nf hset
  have hnorm : ∀ k (hk : k ≤ m), ‖fun j => ((φ (F k hk ((Fintype.equivFin _).symm j)) : ↥(intO ↥C.S)) : ↥C.S)‖ =
      ∏ l : Fin k, Nf (Fin.castLE hk l) := by
    intro k hk
    haveI : Nonempty (Fin (Fintype.card (Fin k → Fin (M + 1)))) := ⟨Fintype.equivFin _ (fun _ => 0)⟩
    rw [norm_eq_iSup, hprod k hk]
    refine ((Fintype.equivFin _).symm.iSup_comp (g := fun σ => ‖ψ (F k hk σ)‖)).trans ?_
    congr 1
    funext σ
    simp only [F, map_sum, map_mul, map_prod, map_minor]
  rw [hnorm, hnorm, Fin.prod_univ_castSucc, mul_comm]
  rfl

end GlobalTheory.HTLine.GrMinor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPolarization
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.DRFlag (basPull basPull_apply basPull_repr tanPull_tanPull exists_affine_basis)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitGen

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_basis_push {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
    {S : Type} [CommRing S] {x' : Sp S ⟶ X'} {x : Sp S ⟶ X} (e : x' ≫ f = x) {n : ℕ}
    (b : Module.Basis (Fin n) S (TanM x' t'.G)) :
    ∃ b' : Module.Basis (Fin n) S (TanM x t.G), ∀ i, (tv (b' i)).left = (tv (b i)).left ≫ m.φ := by
  subst e
  exact ⟨b.map (tanEquiv m.cart x'), fun i => tanPush_left m.cart x' (b i)⟩

theorem exists_basis_lift {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
    {S : Type} [CommRing S] (x' : Sp S ⟶ X') {x : Sp S ⟶ X} (e : x' ≫ f = x) {n : ℕ}
    (b : Module.Basis (Fin n) S (TanM x t.G)) :
    ∃ b' : Module.Basis (Fin n) S (TanM x' t'.G), ∀ i, (tv (b' i)).left ≫ m.φ = (tv (b i)).left := by
  subst e
  refine ⟨b.map (tanEquiv m.cart x').symm, fun i => (tanPush_left m.cart x' _).symm.trans ?_⟩
  exact congrArg (fun v => (tv v).left) ((tanEquiv m.cart x').apply_symm_apply (b i))

theorem tv_hom {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} (v : TanM x t.G) :
    (tv v).left ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x := Over.w (tv v)

theorem exists_basis_extends {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {Z : Scheme.{0}} {t : SAB H (Sp R)}
    {tC : SAB H Z} {u : SAB H (Sp (FractionRing R))} {x : Sp (FractionRing R) ⟶ Z} (hu : IsProper u.G.hom)
    (aT : SABMap u t (jK R)) (aC : SABMap u tC x) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (FractionRing R) (TanM x tC.G)),
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V), (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ (χ : Sp V ⟶ Z) (h : spMap gam ≫ x = jK V ≫ χ), ∃ b' : Module.Basis (Fin n) V (TanM χ tC.G), ∀ i,
        tanPull gam h (b i) = tanPull (algebraMap V (FractionRing V)) rfl (b' i) := by
  obtain ⟨U, n, hU, hb⟩ := exists_affine_basis t (closedPoint R)
  obtain ⟨bR⟩ := hb R (𝟙 _) ((IsLocalRing.closed_point_mem_iff (U := U)).1 hU).ge
  obtain ⟨bu, hbu⟩ := exists_basis_lift aT (𝟙 _) (Category.id_comp _)
    (basPull (algebraMap R (FractionRing R)) (Category.comp_id _) bR)
  obtain ⟨b, hb⟩ := exists_basis_push aC (Category.id_comp _) bu
  refine ⟨n, b, fun V _ _ _ hV ψ gam hg χ h => ?_⟩
  obtain ⟨Dd, tW, c0, mm, a1, a3, -, e₁, e₂⟩ := exists_trait_map hu aT aC hV ψ gam hg χ h
  obtain ⟨bw, hbw⟩ := exists_basis_lift a1 (𝟙 _) (Category.id_comp _) (basPull ψ (Category.comp_id _) bR)
  obtain ⟨b', hb'⟩ := exists_basis_push a3 (Category.id_comp _) bw
  refine ⟨b', fun i => tan_ext_left ?_⟩
  simp only [basPull_apply, tanPull_left] at hbu hbw
  rw [tanPull_left, tanPull_left, hb, hb']
  have w : (spMap (dualMap gam) ≫ (tv (bu i)).left) ≫ u.G.hom =
      spMap (algebraMap _ (DualNumber (FractionRing V))) ≫ spMap gam := by
    rw [Category.assoc, tv_hom, Category.comp_id, spMap_comp', spMap_comp', PullbackSections.dualMap_comp_alg]
  obtain ⟨ρ, ρ₁, ρ₂⟩ : ∃ ρ : Sp (DualNumber (FractionRing V)) ⟶ Dd.G.left,
      ρ ≫ c0.φ = spMap (dualMap gam) ≫ (tv (bu i)).left ∧
      ρ ≫ Dd.G.hom = spMap (algebraMap _ (DualNumber (FractionRing V))) :=
    ⟨c0.cart.1.lift _ _ w, c0.cart.1.lift_fst _ _ w, c0.cart.1.lift_snd _ _ w⟩
  have hc : gam.comp (algebraMap R _) = (algebraMap V _).comp ψ := RingHom.ext hg
  have k : ρ ≫ mm.φ = spMap (dualMap (algebraMap V (FractionRing V))) ≫ (tv (bw i)).left := by
    apply a1.cart.1.hom_ext
    · rw [Category.assoc, ← e₁, reassoc_of% ρ₁, hbu, Category.assoc, hbw, ← Category.assoc, ← Category.assoc,
        spMap_comp', spMap_comp', ← FlagMod.dualMap_comp, ← FlagMod.dualMap_comp, hc]
    · rw [Category.assoc, mm.cart.1.w, reassoc_of% ρ₂, Category.assoc, tv_hom, Category.comp_id, spMap_comp',
        spMap_comp', PullbackSections.dualMap_comp_alg]
  rw [← reassoc_of% ρ₁, e₂, reassoc_of% k]

end Lie

theorem gm_eq_of_ev {F : Type} [Field F] {X X' : Scheme.{0}} (r : Sp F ⟶ X) (r' : Sp F ⟶ X') (z : Sp F) {U : X.Opens}
    {U' : X'.Opens} (h : ⊤ ≤ r ⁻¹ᵁ U) (h' : ⊤ ≤ r' ⁻¹ᵁ U') {a : Γ(X, U)ˣ} {a' : Γ(X', U')ˣ}
    (e : ev r U h a.val = ev r' U' h' a'.val) : gm r z U a = gm r' z U' a' := by
  have e' : (r.appLE U ⊤ h).hom a.val = (r'.appLE U' ⊤ h').hom a'.val :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).hom).1 e
  apply Units.ext
  rw [gm_val r z U (h trivial), gm_val r' z U' (h' trivial)]
  exact ((Sp F).presheaf.germ_res_apply (homOfLE h) z trivial _).symm.trans
    ((congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom e').trans
      ((Sp F).presheaf.germ_res_apply (homOfLE h') z trivial _))

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {S : Type} [CommRing S]

theorem exists_spMap {T : Type} [CommRing T] (z : Sp T ⟶ Sp S) : ∃ φ : S →+* T, spMap φ = z :=
  ⟨(Spec.preimage z).hom, Spec.map_preimage z⟩

theorem exists_unit_chart (y : Sp S ⟶ Z.X) {n : ℕ} (b : Module.Basis (Fin n) S (TanM y Z.t.G)) (M : MChart Z) :
    ∃ u : Γ(Sp S, y ⁻¹ᵁ M.U)ˣ, ∀ (T : Type) [CommRing T] (φ : S →+* T) (h : ⊤ ≤ spMap φ ⁻¹ᵁ (y ⁻¹ᵁ M.U))
      (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x) (h' : ⊤ ≤ x ⁻¹ᵁ M.U),
      ev (spMap φ) _ h u.val = rdet ((basPull φ e b).toMatrix (lieBasis M x h')) := by
  have ha : IsAffineOpen (y ⁻¹ᵁ M.U) := by
    have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
    have h := isAffineOpen_inf_preimage Z.s y M.hU (isAffineOpen_top (Sp S))
    rwa [top_inf_eq] at h
  obtain ⟨τ, hτ⟩ := exists_spMap (tau ha)
  have h₀ : ⊤ ≤ (spMap τ ≫ y) ⁻¹ᵁ M.U := by rw [hτ]; exact le_preimage_map y le_rfl (tau_le _ le_rfl)
  refine ⟨(isUnit_rdet_toMatrix (basPull τ rfl b) (lieBasis M (spMap τ ≫ y) h₀)).unit, fun T _ φ h x e h' => ?_⟩
  have e₀ : spMap (ev (spMap φ) _ h) ≫ spMap τ = spMap φ := by rw [hτ]; exact spMap_ev _ ha h
  have e₁ : spMap (ev (spMap φ) _ h) ≫ spMap τ ≫ y = x := by rw [reassoc_of% e₀, e]
  have e₂ : (ev (spMap φ) _ h).comp τ = φ :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((spMap_comp' _ _).symm.trans e₀))
  have e₃ : basPull φ e b = basPull _ e₁ (basPull τ rfl b) := Module.Basis.eq_of_apply_eq fun i => by
    rw [basPull_apply, basPull_apply, basPull_apply, tanPull_tanPull _ _ _ _ (by rw [e₂, e])]
    apply tan_ext_left
    rw [tanPull_left, tanPull_left, e₂]
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  rw [e₃, Module.Basis.toMatrix_apply, ← tanPull_lieBasis M _ e₁ h₀ h', basPull_repr]
  rfl

theorem exists_gen_basis (y : Sp S ⟶ Z.X) {n : ℕ} (b : Module.Basis (Fin n) S (TanM y Z.t.G)) :
    ∃ g : LB.Gen ((detOm Z).pull y), g.IsGen ∧ ∀ (j : PUnit → MChart Z) (T : Type) [CommRing T] (φ : S →+* T)
      (h : ⊤ ≤ spMap φ ⁻¹ᵁ ((detOm Z).pull y).U j) (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x)
      (h' : ⊤ ≤ x ⁻¹ᵁ (j PUnit.unit).U),
      ev (spMap φ) _ h (g.s j).val = rdet ((basPull φ e b).toMatrix (lieBasis (j PUnit.unit) x h')) := by
  choose u hu using exists_unit_chart y b
  have le : ∀ j : PUnit → MChart Z, ((detOm Z).pull y).U j ≤ y ⁻¹ᵁ (j PUnit.unit).U := fun j =>
    LB.wchart_le (detOm Z) (fun _ : PUnit => y) j PUnit.unit
  have v : ∀ (j : PUnit → MChart Z) (T : Type) [CommRing T] (φ : S →+* T)
      (h : ⊤ ≤ spMap φ ⁻¹ᵁ ((detOm Z).pull y).U j) (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x)
      (h' : ⊤ ≤ x ⁻¹ᵁ (j PUnit.unit).U),
      ev (spMap φ) _ h (res (le j) (u (j PUnit.unit))).val =
        rdet ((basPull φ e b).toMatrix (lieBasis (j PUnit.unit) x h')) := fun j T _ φ h x e h' =>
    (ev_res _ (le j) h (le_preimage_mono (le j) h) _).trans (hu _ T φ _ x e h')
  refine ⟨⟨fun j => res (le j) (u (j PUnit.unit))⟩, fun i j => Units.ext (ext_ev fun T _ z hz => ?_), v⟩
  obtain ⟨φ, rfl⟩ := exists_spMap z
  have hi := le_preimage_mono inf_le_left hz
  have hj := le_preimage_mono inf_le_right hz
  have hi' := le_preimage_map y (le i) hi
  have hj' := le_preimage_map y (le j) hj
  have g := ev_pull_g (detOm Z) y (spMap φ) i j hz (le_preimage_inf hi' hj')
  have d := ev_detChg (i PUnit.unit) (j PUnit.unit) _ hi' hj' (le_preimage_inf hi' hj')
  have o : ev (spMap φ ≫ y) _ (le_preimage_inf hi' hj') ((detOm Z).g (i PUnit.unit) (j PUnit.unit)).val *
      ev (spMap φ ≫ y) _ (le_preimage_inf hi' hj') (detChg (i PUnit.unit) (j PUnit.unit)).val = 1 :=
    (map_mul _ _ _).symm.trans ((congrArg _ (detChg (i PUnit.unit) (j PUnit.unit)).inv_mul).trans (map_one _))
  refine ((ev_res _ _ hz hi _).trans (v i T φ hi _ rfl hi')).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) g ((ev_res _ _ hz hj _).trans (v j T φ hj _ rfl hj')))).symm)
  rw [← rdet_toMatrix_mul _ (lieBasis (i PUnit.unit) _ hi') (lieBasis (j PUnit.unit) _ hj'), ← d, _root_.mul_left_comm]
  exact (_root_.mul_one _).symm.trans (congrArg _ o.symm)

theorem exists_detOm_gen_extAt {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {t : SAB H (Sp R)}
    {u : SAB H (Sp (FractionRing R))} {x : Sp (FractionRing R) ⟶ Z.X} (hu : IsProper u.G.hom)
    (aT : SABMap u t (jK R)) (aC : SABMap u Z.t x) :
    ∃ e : LB.Gen ((detOm Z).pull x), e.IsGen ∧ ExtAt (detOm Z) x e := by
  obtain ⟨n, b, hb⟩ := exists_basis_extends hu aT aC
  obtain ⟨e, he, ve⟩ := exists_gen_basis x b
  refine ⟨e, he, fun V _ _ _ hV ψ gam hg χ h => ?_⟩
  obtain ⟨b', hb'⟩ := hb V hV ψ gam hg χ h
  obtain ⟨e', he', ve'⟩ := exists_gen_basis χ b'
  refine ⟨e', he', fun z J hJ => ?_⟩
  have top : ∀ {X : Scheme.{0}} (r : Sp (FractionRing V) ⟶ X) (U : X.Opens), r z ∈ U → ⊤ ≤ r ⁻¹ᵁ U := fun r U hz p _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) p z]
    exact hz
  have h₀ := top _ _ (hJ (jK V ≫ χ))
  have h₁ : ⊤ ≤ spMap gam ⁻¹ᵁ ((detOm Z).pull x).U fun _ => J (jK V ≫ χ) :=
    top _ _ (mem_pull.2 (show (spMap gam ≫ x) z ∈ _ by rw [h]; exact hJ _))
  have h₂ : ⊤ ≤ jK V ⁻¹ᵁ ((detOm Z).pull χ).U fun _ => J (jK V ≫ χ) := top _ _ (mem_pull.2 (hJ (jK V ≫ χ)))
  rw [val_of e _ z J (fun _ => J (jK V ≫ χ)) (fun _ => by rw [h]), val_of e' _ z J (fun _ => J (jK V ≫ χ)) (fun _ => rfl)]
  refine gm_eq_of_ev _ _ z h₁ h₂ ((ve _ _ gam h₁ _ h h₀).trans (Eq.trans ?_ (ve' _ _ _ h₂ _ rfl h₀).symm))
  rw [show basPull gam h b = basPull (algebraMap V (FractionRing V)) rfl b' from
    Module.Basis.eq_of_apply_eq fun i => by rw [basPull_apply, basPull_apply, hb']]

end Gen

theorem exists_detOm_gen_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ e : LB.Gen ((GlobalTheory.FlagMod.detOm Z).pull (x₀ ≫ Z.j)), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.FlagMod.detOm Z) (x₀ ≫ Z.j) e := by
  intro E _ _ _ H D l Xo c p W _ _ Z Y bV hbV f t m₁ m₂ _ _ _ O' _ _ _ b' ϖ a χ₀ hO _ x₀ hx
  have : IsLocalRing O' := by
    rcases hO with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.toField.instIsLocalRing
    · infer_instance
  obtain ⟨tR, ⟨mt⟩⟩ := exists_sabPull χ₀ Y.t
  obtain ⟨u, ⟨n₀⟩⟩ := exists_sabPull x₀ Z.oF.t
  obtain ⟨aC, -⟩ := LevelCover.sab_comp n₀ Z.m (e := x₀ ≫ Z.j) rfl
  obtain ⟨n₁, -⟩ := LevelCover.sab_comp n₀ Z.m0.toSABMap rfl
  obtain ⟨n₂, -⟩ := LevelCover.sab_cancel Y.m0.toSABMap n₁ x₀ rfl
  obtain ⟨n₃, -⟩ := LevelCover.sab_comp n₂ Y.m (e := x₀ ≫ Y.j) rfl
  obtain ⟨aT, -⟩ := LevelCover.sab_cancel mt n₃ (jK _) hx
  have hu : IsProper u.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper
  exact exists_detOm_gen_extAt hu aT aC

end GlobalTheory.TraitGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannFormFramePoint
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.ShFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem oF_pt_ext {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {R : Type} [CommRing R] {w w' : Sp R ⟶ Z.oF.t.G.left}
    (h0 : w ≫ Z.m0.toSABMap.φ = w' ≫ Z.m0.toSABMap.φ) (h : w ≫ Z.m.φ ≫ Z.t.G.hom = w' ≫ Z.m.φ ≫ Z.t.G.hom) : w = w' := by
  refine Z.m0.toSABMap.cart.1.hom_ext h0 ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, ← Z.m0.toSABMap.cart.1.w]
    rw [reassoc_of% h0]
  · rw [← Z.jQ_over]
    obtain ⟨g, hg⟩ := Spec.map_surjective (w ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ pullback.snd Z.s (spMap (algebraMap (𝓞 c.F) c.F)))
    obtain ⟨g', hg'⟩ := Spec.map_surjective (w' ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ pullback.snd Z.s (spMap (algebraMap (𝓞 c.F) c.F)))
    have e1 : ∀ v : Sp R ⟶ Z.oF.t.G.left, (v ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ pullback.snd _ _) ≫
        spMap (algebraMap (𝓞 c.F) c.F) = (v ≫ Z.m.φ ≫ Z.t.G.hom) ≫ Z.s := fun v => by
      simp only [Category.assoc, ← pullback.condition]
      rw [← reassoc_of% Z.m.cart.1.w]
    have hh : Spec.map g ≫ spMap (algebraMap (𝓞 c.F) c.F) = Spec.map g' ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [hg, hg', e1, e1, h]
    rw [← Spec.map_comp, ← Spec.map_comp] at hh
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
    have h3 : g.hom = g'.hom := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (by simpa using h2)
    simp only [Category.assoc]
    rw [← hg, ← hg', CommRingCat.hom_ext h3]

end
end GlobalTheory.ShFam

namespace GlobalTheory.ShFam.ToroidalCompactificationData

theorem hodge_gram_of_sameVec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (W : UnfWit (s.U σ)) (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab κ.c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), IsRiem W.F i P Hm → ∀ (q : FrPt (S.Xo κ.l) κ.c (CAt σ)) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Fin W.g → ℂ)), AnLie W.F i P q z → ∀ (y : CxPts (genStr s.T.Z) σ), cxPt s.T.Z q = y → ∀ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ s.T.Z.oF.t.G.left, w ≫ s.T.Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ s.T.Z.m.φ = f.v τ k) → ∀ τ a b, (x.hodge σ).gram y f τ a b = (Real.pi : ℂ) * hermForm Hm (z τ b) (z τ a) := by
  intro D A N j S κ s x σ hσ W i P hP Hm hH q z hq y hy f hf τ a b
  subst hy
  have hv : ∀ τ k, f.v τ k = (cxFrame s.T.Z q).v τ k := by
    intro τ k
    obtain ⟨w, hw0, hw⟩ := hf τ k
    obtain ⟨w', -, hw0', hw'⟩ := EigFrame.ofFrPt_v (S := CAt σ) s.T.Z q (Category.assoc _ _ _).symm τ k
    have hb : w ≫ s.T.Z.m.φ ≫ s.T.Z.t.G.hom = w' ≫ s.T.Z.m.φ ≫ s.T.Z.t.G.hom := by
      rw [reassoc_of% hw, reassoc_of% hw', (f.tan τ k).1]
      exact ((cxFrame s.T.Z q).tan τ k).1.symm
    have e : w = w' := oF_pt_ext (hw0.trans hw0'.symm) hb
    rw [← hw, e]
    exact hw'
  have hco : (cxFrame s.T.Z q).co f τ = 1 := by
    refine EigFrame.co_eq fun k => ?_
    rw [hv τ k]
    convert isCombAtG_single _ _ ((cxFrame s.T.Z q).tan τ) k using 1
    funext a
    simp [Matrix.one_apply, Pi.single_apply]
  rw [(x.hodge σ).change _ (cxFrame s.T.Z q) f τ, hco, x.hodge_gram_riemann hσ W hP hH hq τ]
  simp

end GlobalTheory.ShFam.ToroidalCompactificationData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_of_unity_and_p_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → (∀ N : ℕ, N ∣ l.A → ∃ ζ : ↥(c.V W), IsPrimitiveRoot ζ N) ∧ (IsGalois ℚ E → ∃ a : ↥(c.V W), (p : ↥(c.V W)) ∈ (Ideal.span {a}).radical ∧ ∀ (C : SCF p) (φ : ↥(c.V W) →+* ↥(intO ↥C.S)), Real.log ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ = -(vDiff E p * Real.log p)) := by
  first | exact @GlobalTheory.HTConst.const_main | exact GlobalTheory.HTConst.const_main | (intros; apply GlobalTheory.HTConst.const_main <;> assumption)
end

