import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsUnitTermZero
section
noncomputable section

open IsLocalRing GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.PreModel

open TateSys

section
variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : VPre bar q W A)

theorem term_mem (y : Φ.Y) (mu : Fin s → Φ.X y) (c : Φ.Q) (j : ℕ) (h : (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) :
    Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := by
  refine Ideal.mul_mem_left _ _ ?_
  have h0 : ∀ i, 0 ≤ qW W (Φ.δ y i) mu := fun i => qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) mu
  have h1 : mono W (Φ.t y) (Φ.δ y) mu ∈ maximalIdeal (Φ.V y) ^ ∑ i, (qW W (Φ.δ y i) mu).toNat := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Φ.t_mem y i).1 _
  refine Ideal.pow_le_pow_right ?_ h1
  have : ((∑ i, (qW W (Φ.δ y i) mu).toNat : ℕ) : ℤ) = ∑ i, qW W (Φ.δ y i) mu := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h0 i)
  omega

theorem isClassSum_unique (y : Φ.Y) (N : ℕ) (κ : Fin s → Φ.X y) (c : Φ.Q) {x x' : Φ.V y}
    (h : Φ.IsClassSum y N κ c (RingHom.id _) x) (h' : Φ.IsClassSum y N κ c (RingHom.id _) x') : x = x' := by
  classical
  haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
  have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (Φ.V y)) (maximalIdeal.isMaximal _).ne_top
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hb, Ideal.mem_iInf]
  intro j
  obtain ⟨S, a1, a2, a3⟩ := h j
  obtain ⟨S', b1, b2, b3⟩ := h' j
  simp only [RingHom.id_apply] at a3 b3
  have e1 := Finset.sum_sdiff (f := fun mu => Φ.term y mu c) (Finset.inter_subset_left (s₁ := S) (s₂ := S'))
  have e2 := Finset.sum_sdiff (f := fun mu => Φ.term y mu c) (Finset.inter_subset_right (s₁ := S) (s₂ := S'))
  have m1 : ∑ mu ∈ S \ (S ∩ S'), Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := Ideal.sum_mem _ fun mu hmu => by
    obtain ⟨p, p'⟩ := Finset.mem_sdiff.1 hmu
    exact term_mem Φ y mu c j (b2 mu (a1 mu p) fun r => p' (Finset.mem_inter.2 ⟨p, r⟩))
  have m2 : ∑ mu ∈ S' \ (S ∩ S'), Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := Ideal.sum_mem _ fun mu hmu => by
    obtain ⟨p, p'⟩ := Finset.mem_sdiff.1 hmu
    exact term_mem Φ y mu c j (a2 mu (b1 mu p) fun r => p' (Finset.mem_inter.2 ⟨r, p⟩))
  have : x - x' = (x - ∑ mu ∈ S, Φ.term y mu c) - (x' - ∑ mu ∈ S', Φ.term y mu c) +
      ∑ mu ∈ S \ (S ∩ S'), Φ.term y mu c - ∑ mu ∈ S' \ (S ∩ S'), Φ.term y mu c := by
    rw [← e1, ← e2]; ring
  rw [this]
  exact sub_mem (add_mem (sub_mem a3 b3) m1) m2

theorem exists_isUnit_term_zero (y : Φ.Y) : ∃ c : Φ.Q, IsUnit (Φ.term y (0 : Fin s → Φ.X y) c) := by
  obtain ⟨c, hc⟩ := Φ.u_unit y 0
  exact ⟨c, by simpa [VPre.term, mono, qW] using hc⟩

theorem exists_rescale : ∃ v : ∀ y, (Φ.V y)ˣ, ∀ y : (Φ.rescale v).Y, ∃ c : (Φ.rescale v).Q,
    (Φ.rescale v).term y (0 : Fin s → (Φ.rescale v).X y) c = 1 := by
  choose c hc using fun y => Φ.u_unit y 0
  have key : ∀ y : Φ.Y, Φ.u y 0 (c y) * ((hc y).unit⁻¹ : (Φ.V y)ˣ) * mono W (Φ.t y) (Φ.δ y) 0 = 1 := fun y => by
    simp [mono, qW]
  exact ⟨fun y => (hc y).unit⁻¹, fun y => ⟨c y, key y⟩⟩

theorem low_finite (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (j : ℕ) :
    {mu | P mu ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}.Finite := by
  obtain ⟨c₀, hc₀, hq⟩ := GlobalTheory.Poinc.QWDom.qW_ge s W Φ.posW
  let D : LinearMap.BilinForm ℤ (Φ.X y) := ∑ i, Φ.δ y i
  have hD : ∀ x, D x x = ∑ i, Φ.δ y i x x := fun x => by simp [D, LinearMap.sum_apply]
  have hDs : ∀ a b, D a b = D b a := fun a b => by
    simp only [D, LinearMap.sum_apply]; exact Finset.sum_congr rfl fun i _ => (Φ.bal y i).1 a b
  have hDp : ∀ x, x ≠ 0 → 0 < D x x := fun x hx => by
    rw [hD]
    obtain ⟨i, hi⟩ := Φ.pos y x hx
    exact lt_of_lt_of_le hi (Finset.single_le_sum (f := fun i => Φ.δ y i x x) (fun i _ => Φ.nonneg y i x) (Finset.mem_univ i))
  refine (Set.Finite.pi' fun _ : Fin s => GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite _ D hDs hDp ⌈(j : ℝ) / c₀⌉).subset ?_
  rintro mu ⟨-, hmu⟩ u
  have h1 : ∀ i, c₀ * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) ≤ (qW W (Φ.δ y i) mu : ℝ) := fun i =>
    hq _ (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) mu
  have h2 : c₀ * ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) ≤ ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) := by
    have : ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) = ∑ i, ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) := by
      simp only [hD]; push_cast; exact Finset.sum_comm
    rw [this, Finset.mul_sum]; push_cast
    exact Finset.sum_le_sum fun i _ => by exact_mod_cast h1 i
  have h3 : (D (mu u) (mu u) : ℝ) ≤ ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) := by
    exact_mod_cast Finset.single_le_sum (f := fun u => D (mu u) (mu u)) (fun u _ => by
      by_cases h : mu u = 0
      · simp [h]
      · exact (hDp _ h).le) (Finset.mem_univ u)
  have h4 : ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) < j := by exact_mod_cast hmu
  have h5 : (D (mu u) (mu u) : ℝ) ≤ (j : ℝ) / c₀ := by
    rw [le_div_iff₀' hc₀]; nlinarith
  show D (mu u) (mu u) ≤ ⌈(j : ℝ) / c₀⌉
  exact_mod_cast h5.trans (Int.le_ceil _)

theorem exists_sum (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (c : Φ.Q) : ∃ x : Φ.V y, ∀ j : ℕ,
    ∃ S : Finset (Fin s → Φ.X y), (∀ mu ∈ S, P mu) ∧ (∀ mu, P mu → mu ∉ S → (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) ∧
      x - ∑ mu ∈ S, Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := by
  classical
  haveI : IsAdicComplete (maximalIdeal (Φ.V y)) (Φ.V y) := (Φ.cn y).2.2.1
  let S : ℕ → Finset (Fin s → Φ.X y) := fun j => (low_finite Φ y P j).toFinset
  have hS : ∀ j mu, mu ∈ S j ↔ P mu ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ) := fun j mu => Set.Finite.mem_toFinset _
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (I := maximalIdeal (Φ.V y)) (M := Φ.V y) inferInstance
    (f := fun j => ∑ mu ∈ S j, Φ.term y mu c) (by
      intro m n hmn
      have hsub : S m ⊆ S n := fun mu hmu => by
        rw [hS] at hmu ⊢; exact ⟨hmu.1, hmu.2.trans_le (by exact_mod_cast hmn)⟩
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Finset.sum_sdiff hsub, sub_add_cancel_right]
      refine neg_mem (Ideal.sum_mem _ fun mu hmu => ?_)
      obtain ⟨p, p'⟩ := Finset.mem_sdiff.1 hmu
      refine term_mem Φ y mu c m ?_
      by_contra h
      exact p' ((hS m mu).2 ⟨((hS n mu).1 p).1, by omega⟩))
  refine ⟨x, fun j => ⟨S j, fun mu h => ((hS j mu).1 h).1, fun mu h hn => ?_, ?_⟩⟩
  · by_contra h'
    exact hn ((hS j mu).2 ⟨h, by omega⟩)
  · have := (hx j).symm
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this

def lim (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (c : Φ.Q) : Φ.V y := (exists_sum Φ y P c).choose

theorem isClassSum_lim (y : Φ.Y) (N : ℕ) (κ : Fin s → Φ.X y) (c : Φ.Q) :
    Φ.IsClassSum y N κ c (RingHom.id _) (lim Φ y (fun mu => ∀ v, CongMod N (mu v) (κ v)) c) :=
  (exists_sum Φ y _ c).choose_spec
end

theorem tate_exact (N : ℕ) : VSys.tate.pre.Exact N := fun y κ c => ⟨_, isClassSum_lim _ y N κ c⟩

theorem tate_classSums (N₁ : ℕ) (hN : 1 ≤ N₁) : VSys.tate.pre.ClassSums N₁ := by
  intro y₀ N₀
  let A := PowerSeries ℚ
  let L := FractionRing A
  have hbij : Function.Bijective (algebraMap A (integralClosure A L)) := by
    refine ⟨fun a b h => IsFractionRing.injective A L (congrArg Subtype.val h), fun x => ?_⟩
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).1 x.2
    exact ⟨a, Subtype.ext ha⟩
  let E : A ≃+* integralClosure A L := RingEquiv.ofBijective _ hbij
  let M := N₁ * (N₀ + 1)
  refine ⟨M, by show N₀ ≤ N₁ * (N₀ + 1); nlinarith, by show 1 ≤ N₁ * (N₀ + 1); nlinarith, dvd_mul_right _ _, fun _ => (LinearMap.id : ℤ →ₗ[ℤ] ℤ), rfl,
    fun _ => ⟨fun c x => ⟨0, by rw [smul_zero, add_zero]; rfl⟩, LinearEquiv.refl ℤ ℤ, by
      show _ ∣ LinearMap.det ((LinearEquiv.refl ℤ ℤ).toLinearMap ∘ₗ (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) - 1
      simp⟩,
    L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (maximalIdeal A).comap E.symm.toRingHom,
    fun κ c => E (lim VSys.tate.pre y₀ (fun mu => ∀ v, CongMod M (mu v) (κ v)) c),
    Ideal.comap_isMaximal_of_surjective _ E.symm.surjective, ?_, ?_, ?_⟩
  · intro κ κ' c h
    have hP : (fun mu : Fin 1 → VSys.tate.pre.X y₀ => ∀ v, CongMod M (mu v) (κ v)) =
        (fun mu => ∀ v, CongMod M (mu v) (κ' v)) := by
      funext mu
      refine propext (forall_congr' fun u => ⟨fun h' => GlobalTheory.Poinc.OrbTrace.cm_trans h' (h u),
        fun h' => GlobalTheory.Poinc.OrbTrace.cm_trans h' (GlobalTheory.Poinc.OrbTrace.cm_symm (h u))⟩)
    show E (lim _ _ _ c) = E (lim _ _ _ c)
    rw [hP]
  · intro y
    refine ⟨VSys.tate.pre.V y, inferInstance, inferInstance, RingHom.id _, (E.symm.toRingHom : integralClosure A L →+* VSys.tate.pre.V y),
      RingHom.Finite.id _, inferInstance, fun I => by rw [Ideal.map_id, Ideal.comap_id], RingHom.ext fun a => E.symm_apply_apply a, rfl,
      fun κ c => ?_⟩
    obtain rfl : y = y₀ := rfl
    have key := isClassSum_lim VSys.tate.pre y M κ c
    have e : (E.symm (E (lim VSys.tate.pre y (fun mu => ∀ v, CongMod M (mu v) (κ v)) c)) : VSys.tate.pre.V y) =
        lim VSys.tate.pre y (fun mu => ∀ v, CongMod M (mu v) (κ v)) c := E.symm_apply_apply _
    exact (congrArg (VSys.tate.pre.IsClassSum y M κ c (RingHom.id _)) e).mpr key
  · intro σ _
    refine ⟨(LinearMap.id : ℤ →ₗ[ℤ] ℤ), fun c (x : ℤ) => (⟨0, by simp⟩ : CongMod _ (c • x) (c • x)),
      (by simp : ((M : ℕ) : ℤ) ∣ LinearMap.det (LinearMap.id : ℤ →ₗ[ℤ] ℤ) - 1),
      fun (x : ℤ) => (⟨0, by simp⟩ : CongMod N₁ x x), fun κ c => σ.commutes _⟩

def const : VPre (O := ℤ) id 1 !![1] ℚ :=
  { posW := VSys.tate.posW, Y := PUnit, V := fun _ => PowerSeries ℚ, cn := fun y => VSys.tate.cn y
    ev := fun _ => PowerSeries.C
    ev_loc := fun _ => ⟨fun a ha => by
      rcases eq_or_ne a 0 with rfl | h
      · simp at ha
      · exact h.isUnit⟩
    X := fun _ => ℤ, rank_le := fun _ => by simp, m := fun _ => 1, t := fun _ _ => PowerSeries.X
    t_mem := fun y => VSys.tate.t_mem y, δ := fun _ _ => LinearMap.mul ℤ ℤ, bal := fun y => VSys.tate.bal y
    nonneg := fun y => VSys.tate.nonneg y, pos := fun y => VSys.tate.pos y, Q := Unit, u := fun _ _ _ => 1
    u_unit := fun _ _ => ⟨(), isUnit_one⟩ }

def cpt : const.Y := PUnit.unit

def toZ (x : const.X cpt) : ℤ := x

theorem not_lam : ¬ const.abelian₂ := by
  rintro ⟨C, hC⟩
  obtain ⟨h, hh, hd⟩ := hC cpt rfl (0 : Fin 1) (show const.X cpt from (1 : ℤ)) (one_ne_zero : (1 : ℤ) ≠ 0)
  have h0 : h = 0 := by rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hh
  subst h0
  rw [map_zero, zero_dvd_iff] at hd
  exact pow_ne_zero _ (PowerSeries.X_ne_zero (R := ℚ)) hd

theorem not_exact : ¬ const.Exact 3 := by
  classical
  intro hE
  let κ : Fin 1 → const.X cpt := fun _ => show const.X cpt from (1 : ℤ)
  obtain ⟨h, hh⟩ := hE cpt κ ()
  obtain ⟨S, a1, a2, a3⟩ := hh 2
  have hone : κ ∈ S := by
    by_contra hn
    have h2 := a2 κ (fun _ => ⟨0, by simp⟩) hn
    have h3 : ∑ i : Fin (const.m cpt), qW !![1] (const.δ cpt i) κ = 1 := by
      show ∑ i : Fin 1, qW !![1] (LinearMap.mul ℤ ℤ) (fun _ => (1 : ℤ)) = 1
      simp [qW]
    omega
  have a4 : const.ev cpt h - ∑ mu ∈ S, const.term cpt mu () ∈ maximalIdeal (const.V cpt) ^ 2 := a3
  rw [← Finset.add_sum_erase _ _ hone] at a4
  have a5 : ∑ mu ∈ S.erase κ, const.term cpt mu () ∈ maximalIdeal (const.V cpt) ^ 2 := by
    refine Ideal.sum_mem _ fun mu hmu => term_mem const cpt mu () 2 ?_
    obtain ⟨p, p'⟩ := Finset.mem_erase.1 hmu
    obtain ⟨w, hw⟩ := a1 mu p' (0 : Fin 1)
    have hw' : toZ (mu 0) = 1 + 3 * toZ w := by
      have : toZ (mu 0) = (1 : ℤ) + (3 : ℕ) • toZ w := hw
      rw [this, nsmul_eq_mul]; push_cast; ring
    have hw0 : toZ w ≠ 0 := by
      intro h0
      apply p
      funext a
      rw [Subsingleton.elim a 0]
      show toZ (mu 0) = 1
      rw [hw', h0]; ring
    show ((2 : ℕ) : ℤ) ≤ ∑ i : Fin 1, qW !![1] (LinearMap.mul ℤ ℤ) (fun v => toZ (mu v))
    simp only [Finset.univ_unique, Finset.sum_singleton, qW_mul]
    rw [hw']
    push_cast
    rcases lt_or_gt_of_ne hw0 with h | h <;> nlinarith
  have a6 : const.term cpt κ () = (show const.V cpt from PowerSeries.X) := by
    show (1 : PowerSeries ℚ) * mono !![1] (fun _ : Fin 1 => PowerSeries.X) (fun _ => LinearMap.mul ℤ ℤ) (fun _ => (1 : ℤ)) = PowerSeries.X
    simp only [mono, qW]
    simp
    exact (one_mul _).trans ((pow_one _).trans (pow_one _))
  have a7 : const.ev cpt h - (show const.V cpt from PowerSeries.X) ∈ maximalIdeal (const.V cpt) ^ 2 := by
    have := add_mem a4 a5
    rw [a6] at this
    convert this using 1
    ring
  change (PowerSeries.C h : PowerSeries ℚ) - PowerSeries.X ∈ maximalIdeal (PowerSeries ℚ) ^ 2 at a7
  have a8 : (PowerSeries.C h - PowerSeries.X : PowerSeries ℚ) ∈ Ideal.span {PowerSeries.X ^ 2} := by
    rw [← Ideal.span_singleton_pow, ← PowerSeries.maximalIdeal_eq_span_X]; exact a7
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at a8
  simpa [PowerSeries.coeff_C] using a8 1 (by norm_num)

end GlobalTheory.Poinc.PreModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueAdjoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.MemberTest

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}

theorem existsUnique_adjoint (X₁ : Setup F W i) (a : Matrix (Fin 8) (Fin 8) ℤ) :
    ∃! a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) := by
  have hu : IsUnit (W + W.transpose).det := by rw [X₁.e8.2]; exact isUnit_one
  refine ⟨(W + W.transpose)⁻¹ * (a.transpose * (W + W.transpose)), Matrix.mul_nonsing_inv_cancel_left _ _ hu, fun b hb => ?_⟩
  rw [← hb, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem polar_adjoint {s : ℕ} (S a a' : Matrix (Fin s) (Fin s) ℤ) (h : S * a' = a.transpose * S) (y χ : Fin s → ℤ) :
    (a.mulVec y) ⬝ᵥ (S.mulVec χ) = y ⬝ᵥ (S.mulVec (a'.mulVec χ)) := by
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec y, Matrix.vecMul_transpose]

theorem exists_endU (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : Matrix (Fin 8) (Fin 8) ℤ) :
    ∃ E : EndU 𝔪.U.toUnifPre, E.aA.left ≫ 𝔪.φ = 𝔪.φ ≫ (act a).left :=
  let ⟨a', h, _⟩ := existsUnique_adjoint X₁ a
  let ⟨E, hE, _⟩ := 𝔪.equiv a a' h
  ⟨E, hE⟩

theorem terms_sum (𝔪 : UMem X₁ z₁ act V ev X t δ) {x₀ : X₁.S.Gam} {C : Type} {lab : C → X₁.S.Gam}
    {T : (Fin 8 → X) → C → V} (h : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V)
      (fun χ => algebraMap V (FractionRing V) (T (𝔪.e₈.symm χ) c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)
      (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hs, hc, hT⟩ := h
  have := (hc c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hc c).2.1 th s _ hs (hth (lab c))
  convert this using 2 with χ
  rw [hT, AddEquiv.apply_symm_apply]

theorem exists_frames (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam) :
    ∃ (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x), x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left ∧
      fr.IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl x.left z (J (x.left ≫ 𝔪.φ)) (J' x.left) * val fr (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J := by
  have hp := 𝔪.cart.1
  have e : jFK (R := V) (FractionRing V) = 𝟙 _ := Spec.map_id _
  have hw : (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = jFK (R := V) (FractionRing V) ≫ spMap 𝔪.yK := by
    rw [e, Category.assoc, Over.w]; simp
  let x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A := Over.homMk (hp.lift _ _ hw) (hp.lift_snd _ _ hw)
  have hx : x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := hp.lift_fst _ _ hw
  obtain ⟨fr, hfr, H⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.wl ((isGen_iff _).1 𝔪.wl_gen)
    (K := Fin 1) (fun _ => (X₁.ρ.pt a).left) (fun _ => x.left) (fun _ => 1) (spMap 𝔪.yK) (fun _ => hx) (X₁.ρ.fr a)
    (X₁.ρ.fr_tors a).2.1
  refine ⟨x, fr, hx, hfr, fun z J J' hJ hJ' => ?_⟩
  have := H _ (𝟙 _) z (fun _ => J (x.left ≫ 𝔪.φ)) (fun _ => J' x.left) (fun _ => hJ (x.left ≫ 𝔪.φ)) (fun _ => hJ' x.left)
  rw [val_of fr (𝟙 _) z J' (fun _ => J' x.left) (fun _ => by rw [Category.id_comp]),
    val_of (X₁.ρ.fr a) _ z J (fun _ => J (x.left ≫ 𝔪.φ)) (fun _ => by rw [hx])]
  simpa using this.symm

end GlobalTheory.Poinc.Sep.MemberTest
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInj

section From

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W) (ω : W →+* V)
  {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (D : DegPre V)
  (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 T.B).left)
  (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull β₂))

def From : Prop :=
  IsGrpPullback D.P.A T.B (spMap ω) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ω ≫ (T.c₀ ((n : ℤ) • e a)).left) ∧
    ∀ a b, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      ∀ z J J', Good T.M.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V).left) z ⊤ (unitOn k) *
          (lamVal w (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J J' *
            val (T.τ₀ ((n : ℤ) • e a) ((n : ℤ) • e b)) ((TK V).hom ≫ spMap ω) z J)

def TautPt (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ) (g : GtPtF D F) : Prop :=
  g.b.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left ∧
    ∀ χ, ∃ k : Fˣ, (k : F) = ∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s i)) ^ ε i (e χ) a ∧
      ∀ z J J', Good T.M.L z J → Good D.P.L z J' →
        val (g.s χ) (𝟙 _) z J' = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k) *
          (lamVal w (lift (DegPre.cF D F χ) g.b).left z J J' *
            val (T.τ₀ ((n : ℤ) • e χ) a) ((TF (R := V) F).hom ≫ spMap ω) z J)

end From

section Tr

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def Ext (f : R →+* V) {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F]
    (j : F₀ →+* F) : Prop :=
  ∀ r, j (algebraMap (FractionRing R) F₀ (algebraMap R (FractionRing R) r)) =
    algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (f r))

theorem ext_id (F : Type) [Field F] [Algebra (FractionRing R) F] : Ext (RingHom.id R) (RingHom.id F) := fun _ => rfl

def Tr (f : R →+* V) {D₀ : DegPre R} {D : DegPre V} (hD : IsPullDeg f D₀ D) {F₀ F : Type} [Field F₀]
    [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F) (g₀ : GtPtF D₀ F₀) (g : GtPtF D F) :
    Prop :=
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  ∃ g₁ : GtPtF D₀ F, (g₁.b.left = spMap j ≫ g₀.b.left ∧
    ∀ χ, LB.Gen.Corr D₀.P.L _ _ _ _ (g₁.s χ) (LB.pullGen D₀.P.L _ _ (g₀.s χ) (spMap j))) ∧ IsPullGtF f hD F g₁ g

end Tr

def OverPt {X : Scheme.{0}} {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre h n ζ sX) {S : Scheme.{0}}
    (A : PolAV S) (y : S ⟶ X) (α : A.A.left ⟶ c.A.left) : Prop :=
  IsGrpPullback A.A c.A y α ∧ ∃ α₂ : (G2 A.A).left ⟶ (G2 c.A).left, IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (c.P.pull α₂)

def Match {V : Type} [CommRing V] [IsDomain V] (D₁ D₂ : DegPre V) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F]
    [Algebra (FractionRing V) F] : Prop :=
  IsMonHom b ∧ IsIso b ∧
    LBIso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₂.P.A D₂.P.L).pull
      (lift (fst D₁.P.A D₁.P.A ≫ b) (snd D₁.P.A D₁.P.A ≫ b) : G2 D₁.P.A ⟶ G2 D₂.P.A).left) ∧
    (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (φ.symm.toAddMonoidHom χ) χ), Nrm u) ∧
    ∀ (y : D₁.X) (g : GtPtF D₁ F), GtPtF.IsIota y g →
      ∃ g' : GtPtF D₂ F, Act D₁ D₂ b φ.symm.toAddMonoidHom g g' ∧ GtPtF.IsIota (φ y) g'

def QImg {V : Type} [CommRing V] [IsDomain V] {D₁ D₂ : DegPre V} (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) {F : Type} [Field F]
    [Algebra (FractionRing V) F] {k : ℕ} (p₁ : QkPt D₁ F k) (p₂ : QkPt D₂ F k) : Prop :=
  ∃ p' : QkPt D₂ F k, p'.y = φ p₁.y ∧ Act D₁ D₂ b φ.symm.toAddMonoidHom p₁.g p'.g ∧ QkPt.Equiv D₂ F p' p₂

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CovTest.SwapLine

namespace GlobalTheory.LineForm

def hs (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ j ∈ Finset.range (m + 1), C ((-1) ^ j * ((m - j).choose j : ℝ)) * X 0 ^ (m - 2 * j) * X 1 ^ j

def pm (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ j ∈ Finset.range (m + 1), C ((m.choose j * j.factorial * j.factorial : ℝ) / (2 * j + 1).factorial) *
    X 1 ^ (m - j) * (X 0 ^ 2 - 4 * X 1) ^ j

def upperParabolic {ι : Type} (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 5) ℝ :=
  ∑ x ∈ s, (X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x)

def downP {ι : Type} (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 4) ℝ :=
  ∑ x ∈ s, aeval ![X 1 + X 2, X 3] (pm (m x)) * aeval ![X 0, X 1, X 2] (W x)

def idx (d : ℕ) : Finset (ℕ × ℕ) := (Finset.range (d + 3) ×ˢ Finset.range (d + 3)).filter fun x => x.2 < x.1

def expo (x : ℕ × ℕ) : ℕ := x.1 - 1 - x.2

def coefW (R : ℕ → MvPolynomial (Fin 2) ℝ) (x : ℕ × ℕ) : MvPolynomial (Fin 3) ℝ :=
  (X 1 * X 2) ^ x.2 * aeval ![X 1 + X 2, X 0] (R x.1)

def baseT (d : ℕ) (R : ℕ → MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ x ∈ idx d, X 1 ^ x.2 * aeval ![X 0, X 1] (pm (expo x)) * aeval ![X 0, X 2] (R x.1)

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def fld (w : A.Pt → Ev n) : A.Fld := fun x => w x

def evalF {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) : A.Fld :=
  fld A fun x => aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ))

def wInt [MeasurableSpace M] (g : M → ℝ) (α : A.Fld) : ℝ := ∫ y, g y ∂A.part α 1 - ∫ y, g y ∂A.part α (-1)

theorem wInt_one [MeasurableSpace M] (α : A.Fld) : wInt A (fun _ => 1) α = A.integral α := by
  simp [wInt, HolAtlas.integral]

end Manifold

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {D D' : ℕ}

abbrev lineSC {E : X.Modules} (fl : Vert.Flag E 2) : ShortComplex X.Modules :=
  .mk (fl.ι 1) (Limits.cokernel.π _) (Limits.cokernel.condition _)

theorem lineSC_shortExact {E : X.Modules} (fl : Vert.Flag E 2) : (lineSC fl).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

def frameAt {E : X.Modules} (fl : Vert.Flag E 2) {σ : k →+* ℂ} (y : CxPts p σ) : VBExt.AdaptedChart (lineSC fl) 1 1 :=
  (Met.exists_adapted (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) y).choose

theorem mem_frameAt {E : X.Modules} (fl : Vert.Flag E 2) {σ : k →+* ℂ} (y : CxPts p σ) :
    y ∈ ptsIn p σ (frameAt fl y).U :=
  (Met.exists_adapted (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) y).choose_spec

variable (h : IsRegVar p D) (h' : IsRegVar p' D') (σ : k →+* ℂ)

def c1F (L : HermLB p) (x : (h.atlas σ).Pt) : Ev D :=
  ofValues (ddc (fun v => (L.φ σ).φ (pick (L.φ σ).isLB x.pt) (x.ch.symm v)) x.crd)

def c2F {E : X.Modules} (m : VMetric p E 2) (fl : Vert.Flag E 2) (x : (h.atlas σ).Pt) : Ev D :=
  (h.atlas σ).chern ((m.met σ).gram (frameAt fl x.pt).frame) 2 x

def omF {E : X.Modules} (m : VMetric p E 2) (fl : Vert.Flag E 2) (x : (h.atlas σ).Pt) : Ev D :=
  ofValues (extTrace (fun v => (m.met σ).gram (frameAt fl x.pt).frame (x.ch.symm v)) x.crd)

def fam4 {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) (A : HermLB p) :
    Fin 4 → (h.atlas σ).Pt → Ev D :=
  ![c1F h σ A, c1F h σ (VMetric.grLB fl 0 H), c1F h σ (VMetric.grLB fl 1 H), c2F h σ m fl]

def pullF (π : Y ⟶ X) (w : π ≫ p = p') (α : (h.atlas σ).Fld) : (h'.atlas σ).Fld :=
  (h.atlas σ).pullback (h'.atlas σ) (PtsOver.map π w _) α

end GlobalTheory.LineForm
end
end

