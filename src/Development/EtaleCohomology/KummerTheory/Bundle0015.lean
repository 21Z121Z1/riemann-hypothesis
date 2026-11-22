import Development.EtaleCohomology.KummerTheory.Bundle0012
import Development.EtaleCohomology.KummerTheory.Bundle0001
import Development.EtaleCohomology.TateTwists.Bundle0013
import Development.EtaleCohomology.TateTwists.Bundle0022
import Development.EtaleCohomology.TateTwists.Bundle0007
import Development.EtaleCohomology.KummerTheory.Bundle0013

-- bundled from Development.EtaleCohomology.KummerTheory.AdicLimPfCok
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.CokPf

variable (l : ℕ) [Fact l.Prime]

def T (E : Spc) (n i : ℤ) (k : ℕ) : Submodule ℤ_[l] (Hl l E n i) :=
  LinearMap.ker (((l : ℤ_[l]) ^ k) • (LinearMap.id : Hl l E n i →ₗ[ℤ_[l]] Hl l E n i))

theorem T_mono (E : Spc) (n i : ℤ) : Monotone (T l E n i) := by
  intro a b hab x hx
  simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm, mul_smul, hx, smul_zero]

theorem stab (E : Spc) (n i : ℤ) [Module.Finite ℤ_[l] (Hl l E n i)] :
    ∃ K : ℕ, ∀ m, T l E n i m ≤ T l E n i K := by
  have : IsNoetherian ℤ_[l] (Hl l E n i) := inferInstance
  obtain ⟨K, hK⟩ := monotone_stabilizes_iff_noetherian.mpr this ⟨T l E n i, T_mono l E n i⟩
  refine ⟨K, fun m => ?_⟩
  rcases le_total m K with h | h
  · exact T_mono l E n i h
  · exact (hK m h).symm.le

theorem cok (hA : A11) (E : Spc) (i : ℤ) (hB : ∀ b, BockData l b E i)
    (hFin : ∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) (n : ℤ) [Module.Finite ℤ_[l] (Hl l E (n + 1) i)] :
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨K, hK⟩ := stab l E (n + 1) i
  refine ⟨l ^ K, pow_pos (Fact.out : l.Prime).pos K, fun k z => ?_⟩
  obtain ⟨u, d, h⟩ := hB k
  let D : Hl l E (n + 1) i := ⟨fun a => d a n z, fun a => (h a n).2.2.2.2.1 z⟩
  have hD : D ∈ T l E (n + 1) i k := by
    simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    apply Subtype.ext; funext a
    change (l ^ k) • d a n z = 0
    rw [← map_nsmul, KerPf.smul_zero_of l E n i k k le_rfl, map_zero]
  have hD' := hK k hD
  simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hD'
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hD'
  have hz : ∀ a, d a n ((l ^ K) • z) = 0 := fun a => by
    have := congrArg (fun v : Hl l E (n + 1) i => v.1 a) hD'
    change (l ^ K) • d a n z = 0 at this
    rw [map_nsmul]; exact this
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ (k + a)) E n i // red (l ^ (k + a)) (l ^ k) E n i w = (l ^ K) • z}
  have hS : ∀ a, Finite (S a) := fun a => by have := hFin (k + a) n; exact Subtype.finite
  have hN : ∀ a, Nonempty (S a) := fun a => by
    obtain ⟨w, hw⟩ := ((h a n).2.1 ((l ^ K) • z)).1 (hz a)
    exact ⟨⟨w, hw⟩⟩
  let t : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (k + (a + 1))) (l ^ (k + a)) E n i w.1, by
    rw [(@hA (l ^ (k + (a + 1))) (l ^ (k + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ k)
      (pow_dvd_pow l (by omega)) n i w.1]
    exact w.2⟩
  obtain ⟨s, hs⟩ := KerPf.seqSec S t
  let x : Hl l E n i := ⟨fun j => red (l ^ (k + j)) (l ^ j) E n i (s j).1, fun j => by
    have A := (@hA (l ^ (k + (j + 1))) (l ^ (j + 1)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ j)
      (pow_dvd_pow l (by omega)) n i (s (j + 1)).1
    have B := (@hA (l ^ (k + (j + 1))) (l ^ (k + j)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ j)
      (pow_dvd_pow l (by omega)) n i (s (j + 1)).1
    exact A.trans (B.symm.trans (congrArg (fun w : S j => red (l ^ (k + j)) (l ^ j) E n i w.1) (hs j)))⟩
  exact ⟨x, (s k).2⟩

end LateralTheory.KummerTheory.CokPf

namespace LateralTheory.KummerTheory

theorem AdicCok_holds : AdicCok := fun hA l _ E i hB hFin n _ => CokPf.cok l hA E i hB hFin n

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.CupAWCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AW
variable {R : Type} [CommRing R] {E : Spc} {I J K : Cx R} {n m k : ℤ} {U : Scheme.{0}}

def ev0 (α : Cochain ((chains R).obj E) I n) (s : ℤ) (U : Scheme.{0}) (p : ℕ) (x : Sx E p U) : Sec (I.X s) U :=
  if h : -(p : ℤ) + n = s then ev α p s h U x else 0

theorem ev_delta {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (x : Sx E p U) :
    ev (δ n m α) p t ht U x = Sec.map (I.d s t) (ev α p s hs U x) + m.negOnePow • bd (ev0 α t U) p x := by
  cases p with
  | zero => rw [ev_delta_zero hm α s t hs]; simp [bd]
  | succ p =>
    rw [ev_delta_succ hm α p s t hs]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dif_pos]

def pr (μ : Pair I J K) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (w : ℤ) (U : Scheme.{0})
    (p q : ℕ) (y : Sx E p U) (z : Sx E q U) : Sec (K.X w) U :=
  if h : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w h (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

variable (μ : Pair I J K) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)

theorem mul_ev {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (ev α p s hs U y) (ev β q t ht U z) = pr μ α β w U p q y z := by
  subst hs ht
  rw [pr, dif_pos h]

theorem mul_bd_left {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + (n + 1) = s) (ht : -(q : ℤ) + m = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (bd (ev0 α s U) p y) (ev β q t ht U z) = bd (fun a y => pr μ α β w U a q y z) p y := by
  cases p with
  | zero => simp [bd]
  | succ p =>
    simp only [bd, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dif_pos (by omega), mul_ev]

theorem mul_bd_right {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + (m + 1) = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (ev α p s hs U y) (bd (ev0 β t U) q z) = bd (fun b z => pr μ α β w U p b y z) q z := by
  cases q with
  | zero => simp [bd]
  | succ q =>
    simp only [bd, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dif_pos (by omega), mul_ev]

theorem d_pr {w : ℤ} {p q : ℕ} (h : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w) (y : Sx E p U) (z : Sx E q U) :
    Sec.map (K.d w (w + 1)) (pr μ α β w U p q y z) =
      (pr μ (δ n (n + 1) α) β (w + 1) U p q y z -
        (((n + 1).negOnePow : ℤˣ) : ℤ) • bd (fun a y => pr μ α β (w + 1) U a q y z) p y) +
      (((-(p : ℤ) + n).negOnePow : ℤˣ) : ℤ) • (pr μ α (δ m (m + 1) β) (w + 1) U p q y z -
        (((m + 1).negOnePow : ℤˣ) : ℤ) • bd (fun b z => pr μ α β (w + 1) U p b y z) q z) := by
  rw [pr, dif_pos h, μ.leibniz, Units.smul_def]
  congr 1
  · rw [← mul_ev μ (δ n (n + 1) α) β (s := -(p : ℤ) + n + 1) (t := -(q : ℤ) + m) (by omega) (by omega) rfl,
      ev_delta rfl α p _ _ rfl, ← mul_bd_left μ α β (s := -(p : ℤ) + n + 1) (t := -(q : ℤ) + m) (by omega) (by omega) rfl,
      map_add, Units.smul_def, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, add_sub_cancel_right]
  · rw [← mul_ev μ α (δ m (m + 1) β) (s := -(p : ℤ) + n) (t := -(q : ℤ) + m + 1) (by omega) rfl (by omega),
      ev_delta rfl β q _ _ rfl, ← mul_bd_right μ α β (s := -(p : ℤ) + n) (t := -(q : ℤ) + m + 1) (by omega) rfl (by omega),
      map_add, Units.smul_def, map_zsmul, add_sub_cancel_right]

variable {μ α β} in
theorem aw_eq {hk : n + m = k} {γ : Cochain ((chains R).obj E) K k} (hγ : μ.IsAW hk α β γ) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + k = w) (x : Sx E N U) : ev γ N w h U x = ∑ p : Fin (N + 1), (((m * (p : ℕ)).negOnePow : ℤˣ) : ℤ) •
      pr μ α β w U p (N - p) (x.sub 0 p (by omega)) (x.sub p (N - p) (by omega)) := by
  rw [hγ N w h U x]
  exact Finset.sum_congr rfl fun p _ => by rw [mul_ev, Units.smul_def]

theorem leibniz : LateralTheory.EtaleFoundations.cupflip_aw_leibniz := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ h h1 h2
  refine ev_ext _ _ fun M w' hw' U x => ?_
  obtain ⟨w, rfl⟩ : ∃ w, w' = w + 1 := ⟨w' - 1, by omega⟩
  have hw : -(M : ℤ) + k = w := by omega
  have hb : bd (ev0 γ (w + 1) U) M x = _ :=
    (bd_congr (fun N y e => by rw [ev0, dif_pos (by omega), aw_eq h]) x).trans
      (bd_aw (pr μ α β (w + 1) U) (fun p => (((m * p).negOnePow : ℤˣ) : ℤ))
        (fun p => ((m.negOnePow * (m * p).negOnePow : ℤˣ) : ℤ)) (fun p => by
          push_cast
          rw [mul_add, mul_one, Int.negOnePow_add]
          rcases Int.units_eq_one_or m.negOnePow with e | e <;> simp [e]) M x)
  rw [ev_delta rfl γ M w _ hw, ev_add, ev_units_smul, aw_eq h, aw_eq h1, aw_eq h2, hb, Sec.map, map_sum,
    Units.smul_def, Units.smul_def, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  have hd := d_pr μ α β (w := w) (p := p) (q := M - p) (by omega) (x.sub 0 p (by omega)) (x.sub p (M - p) (by omega))
  rw [Sec.map] at hd
  rw [map_zsmul, hd]
  have e : (-1 : ℤ) ^ (p : ℕ) = ((((p : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) := by simp [Int.coe_negOnePow_natCast]
  rw [e, ← hk, add_mul, one_mul]
  simp only [Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one]
  generalize (m * (p : ℕ)).negOnePow = c
  generalize ((p : ℕ) : ℤ).negOnePow = d
  generalize n.negOnePow = a
  rcases Int.units_eq_one_or m.negOnePow with e | e <;> rw [e] <;> push_cast <;> module

theorem aw_cochain : LateralTheory.EtaleFoundations.cupflip_aw_cochain :=
  LateralTheory.EtaleFoundations.cupflip_aw_cochain_of LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
    (fun _ _ _ _ _ α p s h _ _ g x => ev_res α p s h g x) LateralTheory.EtaleFoundations.cupflip_sub_res_holds

theorem aw_exists : LateralTheory.EtaleFoundations.cupflip_aw_exists := LateralTheory.EtaleFoundations.cupflip_aw_exists_of aw_cochain leibniz

variable {μ α β} in
theorem aw_unique {hk : n + m = k} {γ γ' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk α β γ) (h' : μ.IsAW hk α β γ') :
    γ = γ' := ev_ext _ _ fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm

theorem wd_aw : LateralTheory.EtaleFoundations.cupflip_wd_aw := by
  intro R _ I J K μ E n m k hk
  refine ⟨aw_exists R μ E hk, fun _ _ _ _ => aw_unique, fun α α' β γ γ' h h' N w hw U x => ?_,
    fun α β β' γ γ' h h' N w hw U x => ?_⟩ <;>
  · rw [ev_add, h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [ev_add, map_add, LinearMap.add_apply, smul_add]

theorem wd_cobdry : LateralTheory.EtaleFoundations.cupflip_wd_cobdry := by
  rintro R _ I J K μ E n m k hk α β γ h (⟨n', hn, η, hη⟩ | ⟨m', hm, η, hη⟩)
  · subst hn
    obtain rfl : k = n' + m + 1 := by omega
    obtain ⟨θ, hθ⟩ := aw_cochain R μ E rfl η β.1
    refine ⟨n' + m, rfl, θ, ?_⟩
    rw [leibniz R μ rfl η β.1 θ γ.1 0 hθ (by rw [hη]; exact h)
      (by rw [Cocycle.δ_eq_zero]; exact LateralTheory.EtaleFoundations.isAW_zero_right μ _ _), smul_zero, add_zero]
  · subst hm
    obtain rfl : k = n + m' + 1 := by omega
    obtain ⟨θ, hθ⟩ := aw_cochain R μ E rfl α.1 η
    refine ⟨n + m', rfl, n.negOnePow • θ, ?_⟩
    rw [δ_units_smul, leibniz R μ rfl α.1 η θ 0 γ.1 hθ
      (by rw [Cocycle.δ_eq_zero]; exact LateralTheory.EtaleFoundations.isAW_zero_left μ _ _) (by rw [hη]; exact h), zero_add, smul_smul,
      Int.units_mul_self, one_smul]

theorem wd : LateralTheory.EtaleFoundations.cupflip_wd := LateralTheory.EtaleFoundations.cupflip_wd_of wd_aw wd_cobdry

theorem cup_mk {hk : n + m = k} (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) :
    μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
  pick_spec (wd R μ E hk) α β γ h

end LateralTheory.KummerTheory.AW

theorem LateralTheory.KummerTheory.CupAW_of : LateralTheory.KummerTheory.CupAW := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := AW.aw_exists R μ E hk α β
  exact ⟨γ, hγ, AW.cup_mk μ α β γ hγ⟩

end
end

-- bundled from Development.EtaleCohomology.KummerTheory.NrmMkPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.NrmMkPf

def eta₃ (R : Type) [CommRing R] (P : PSh) (F : Shv R)
    (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom (fun y => a U.unop y.down))
  naturality U V g := by
    refine ModuleCat.free_hom_ext (fun y => ?_)
    simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map, Functor.comp_obj, Functor.comp_map,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (ha _ _ g.unop y.down).symm

def phi (R : Type) [CommRing R] (P : PSh) (F : Shv R)
    (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (free R).obj P ⟶ F :=
  ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (eta₃ R P F a ha) F.property)

theorem phi_gen (R : Type) [CommRing R] (P : PSh) (F : Shv R)
    (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) :
    ((phi R P F a ha).hom.app (op U)).hom (freeGen R P U x) = a U x := by
  have e := congrArg (fun t => (t.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (eta₃ R P F a ha) F.property)
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  refine e.trans ?_
  erw [ModuleCat.freeDesc_apply]
  rfl

theorem aux (R : Type) [CommRing R] {E : Spc} {I : Cx R} (n j : ℤ)
    (φ : ∀ p : ℕ, -(p : ℤ) + n = j → ((free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X j)) (p q : ℕ) (hpq : q = p)
    (hi : -(p : ℤ) = -(q : ℤ)) (hp : -(p : ℤ) + n = j) (hq : -(q : ℤ) + n = j) :
    (((chains R).obj E).XIsoOfEq hi).hom ≫ (chainsXIso R E q).hom ≫ φ q hq = (chainsXIso R E p).hom ≫ φ p hp := by
  subst hpq; simp

end LateralTheory.KummerTheory.NrmMkPf

namespace LateralTheory.KummerTheory
open NrmMkPf in
theorem NrmMk_of : NrmMk := by
  intro R _ E I n a ha
  let φ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ((free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s) :=
    fun p s h => phi R _ (I.X s) (fun U x => a p s h U x) (fun V U g x => ha p s h V U g x)
  refine ⟨Cochain.mk (fun i j hij => if hi : i ≤ 0 then
      (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫
        (chainsXIso R E (-i).toNat).hom ≫ φ ((-i).toNat) j (by omega) else 0), ?_⟩
  intro p s h U x
  unfold ev
  rw [Cochain.mk_v, dif_pos (by omega)]
  rw [aux R n s (fun q hq => φ q s hq) p (-(-(p : ℤ))).toNat (by omega) _ h]
  simp only [Iso.inv_hom_id_assoc]
  exact phi_gen R _ (I.X s) _ _ U x
end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.PlaceResGoodPf
section
noncomputable section

open IsLocalRing

namespace LateralTheory.KummerTheory

attribute [local instance] Ideal.Quotient.field

section
variable {k K : Type} [Field k] [Field K] [Algebra k K] (A : LocalSubring K)

lemma good_sub_mem (hA : PlaceGood k K A) (a : K) (ha : a ∈ A.toSubring) :
    ∃ c : k, (⟨a - algebraMap k K c, sub_mem ha (hA.1 c)⟩ : A.toSubring) ∈ maximalIdeal A.toSubring := by
  obtain ⟨c, hc⟩ := hA.2 a ha
  refine ⟨c, ?_⟩
  rcases hc with h | h
  · have : (⟨a - algebraMap k K c, sub_mem ha (hA.1 c)⟩ : A.toSubring) = 0 := by
      ext; simp [h]
    rw [this]; exact zero_mem _
  · rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    apply h
    have hK : (a - algebraMap k K c) * (w : K) = 1 := by
      simpa using congrArg (fun z : A.toSubring => (z : K)) hw
    rw [inv_eq_of_mul_eq_one_right hK]; exact w.2

end

theorem PlaceResGood_of : PlaceResGood := by
  intro k K _ _ _ _ A hA y S hAS hS Q _ hQ
  let kS : k →+* S := (algebraMap k K).codRestrict S (fun c => hAS (hA.1 c))

  have stepA : ∀ a (ha : a ∈ A.toSubring), ∃ c : k, (⟨a, hAS ha⟩ : S) - kS c ∈ Q := by
    intro a ha
    obtain ⟨c, hc⟩ := good_sub_mem A hA a ha
    refine ⟨c, ?_⟩
    have := hQ (Ideal.mem_map_of_mem (Subring.inclusion hAS) hc)
    convert this using 1
    rfl

  let φ : k →+* S ⧸ Q := (Ideal.Quotient.mk Q).comp kS
  let _ : Algebra k (S ⧸ Q) := φ.toAlgebra
  have hSm : ∀ s, s ∈ Algebra.adjoin A.toSubring {y} → s ∈ S := fun s hs => by rw [hS]; exact hs
  let y' : S := ⟨y, hSm y (Algebra.subset_adjoin (Set.mem_singleton y))⟩
  have gen : ∀ s (hs : s ∈ Algebra.adjoin A.toSubring {y}),
      Ideal.Quotient.mk Q (⟨s, hSm s hs⟩ : S) ∈ Algebra.adjoin k {Ideal.Quotient.mk Q y'} := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx; subst hx
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap r =>
      obtain ⟨c, hc⟩ := stepA r.1 r.2
      have e : Ideal.Quotient.mk Q (⟨algebraMap A.toSubring K r, hSm _ (Subalgebra.algebraMap_mem _ r)⟩ : S)
          = algebraMap k (S ⧸ Q) c := by
        rw [← sub_eq_zero, ← Ideal.Quotient.mk_eq_mk]
        change Ideal.Quotient.mk Q _ - Ideal.Quotient.mk Q (kS c) = 0
        rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hc
      rw [e]; exact Subalgebra.algebraMap_mem _ c
    | add x z hx hz ihx ihz =>
      have : (⟨x + z, hSm _ (add_mem hx hz)⟩ : S) = ⟨x, hSm _ hx⟩ + ⟨z, hSm _ hz⟩ := rfl
      rw [this, map_add]; exact add_mem ihx ihz
    | mul x z hx hz ihx ihz =>
      have : (⟨x * z, hSm _ (mul_mem hx hz)⟩ : S) = ⟨x, hSm _ hx⟩ * ⟨z, hSm _ hz⟩ := rfl
      rw [this, map_mul]; exact mul_mem ihx ihz
  have top : Algebra.adjoin k {Ideal.Quotient.mk Q y'} = ⊤ := by
    refine eq_top_iff.mpr fun t _ => ?_
    obtain ⟨⟨s, hs⟩, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact gen s (by rw [hS] at hs; exact hs)
  have : Algebra.FiniteType k (S ⧸ Q) := ⟨⟨{Ideal.Quotient.mk Q y'}, by simpa using top⟩⟩
  have : Module.Finite k (S ⧸ Q) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ Q)
  have surj := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := S ⧸ Q)).2
  have stepS : ∀ s : S, ∃ c : k, s - kS c ∈ Q := by
    intro s
    obtain ⟨c, hc⟩ := surj (Ideal.Quotient.mk Q s)
    refine ⟨c, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change Ideal.Quotient.mk Q s - φ c = 0
    rw [← hc]; exact sub_self _

  set B := LocalSubring.ofPrime S Q
  refine ⟨fun c => LocalSubring.le_ofPrime S Q (hAS (hA.1 c)), ?_⟩
  intro b hb
  let bb : B.toSubring := ⟨b, hb⟩
  obtain ⟨t, ht⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal Q B.toSubring).surjective
    (Ideal.Quotient.mk (maximalIdeal B.toSubring) bb)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨c, hc⟩ := stepS s
  refine ⟨c, ?_⟩
  by_cases h0 : b = algebraMap k K c
  · exact Or.inl h0
  right
  intro hinv
  have hmem : bb - algebraMap S B.toSubring (kS c) ∈ maximalIdeal B.toSubring := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ht,
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk, ← map_sub, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_comap.mp (show s - kS c ∈ (maximalIdeal B.toSubring).comap (algebraMap S B.toSubring) by
      rw [← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal B.toSubring Q]; exact hc)
  rw [mem_maximalIdeal, mem_nonunits_iff] at hmem
  apply hmem
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
  ext
  change (b - algebraMap k K c) * (b - algebraMap k K c)⁻¹ = 1
  exact mul_inv_cancel₀ (sub_ne_zero.mpr h0)

end LateralTheory.KummerTheory
end
end

