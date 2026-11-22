import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ThetaProj

theorem eStd_swap (g n : ℕ) (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n a b = -eStd g n b a := by
  simp only [eStd]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_eStd_eq (g n : ℕ) (f : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n) :
    ∃ b, ∀ y, eStd g n b y = f y := by
  refine ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)),
    fun y => ?_⟩
  conv_rhs => rw [← Finset.univ_sum_single y, map_sum, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, f (Pi.single j (y j)) = y j * f (Pi.single j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h, h]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

theorem exists_retraction {n d : ℕ} [NeZero n] {Γ : Type} [AddCommGroup Γ] [Module (ZMod n) Γ]
    (T : AddSubgroup Γ) (e : T ≃+ (Fin d → ZMod n)) : ∃ p : Γ →+ T, ∀ t : T, p t = t := by
  let T' : Submodule (ZMod n) Γ := AddSubgroup.toZModSubmodule n T
  let e' : T' →+ (Fin d → ZMod n) :=
    { toFun := fun x => e ⟨x.1, x.2⟩
      map_zero' := map_zero e
      map_add' := fun x y => map_add e ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ }
  obtain ⟨f, hf⟩ := (ZModPerp.baer_of_free (n := n) (Fin d → ZMod n)).extension_property
    T'.subtype T'.subtype_injective (e'.toZModLinearMap n)
  refine ⟨e.symm.toAddMonoidHom.comp f.toAddMonoidHom, fun t => ?_⟩
  have : f t = e t := LinearMap.congr_fun hf ⟨t.1, t.2⟩
  simp [this]

theorem nsmul_eq_zero_of_forall_char {r N : ℕ} [NeZero (r * N)] {Γ : Type} [AddCommGroup Γ]
    [Module (ZMod (r * N)) Γ] (u : Γ) (h : ∀ ψ : Γ →+ ZMod N, ψ u = 0) : r • u = 0 := by
  by_contra hu
  obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := r * N) hu
  apply hf
  have h1 := h ((ZMod.castHom (dvd_mul_left N r) (ZMod N)).toAddMonoidHom.comp f.toAddMonoidHom)
  have h2 : ZMod.castHom (dvd_mul_left N r) (ZMod N) (f u) = 0 := h1
  rw [← ZMod.natCast_zmod_val (f u), map_natCast, ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨k, hk⟩ := h2
  rw [map_nsmul, ← ZMod.natCast_zmod_val (f u), hk, nsmul_eq_mul, ← Nat.cast_mul, ← _root_.mul_assoc,
    Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem sum_char_smul {o M U : Type} [CommRing o] [IsDomain o] [AddCommGroup M] [Module o M]
    [AddCommGroup U] [Fintype U] {N : ℕ} [NeZero N] [Fintype (U →+ ZMod N)]
    (χ : AddChar (ZMod N) o) (hχ : ∀ a, χ a = 1 → a = 0) (ρ : U → M)
    (hρ : ∀ u, (∀ ψ : U →+ ZMod N, ψ u = 0) → ρ u = ρ 0) :
    ∑ ψ : U →+ ZMod N, ∑ u, χ (-ψ u) • ρ u = (Fintype.card U : o) • ρ 0 := by
  have h1 : ∀ u, (∑ ψ : U →+ ZMod N, χ (-ψ u)) • ρ u
      = (∑ ψ : U →+ ZMod N, χ (-ψ u)) • ρ 0 := fun u => by
    by_cases hu : ∀ ψ : U →+ ZMod N, ψ u = 0
    · rw [hρ u hu]
    · obtain ⟨ψ, hψ⟩ := not_forall.mp hu
      have : χ.compAddMonoidHom (-(AddMonoidHom.eval u : (U →+ ZMod N) →+ ZMod N)) ≠ 1 := by
        intro h
        have := DFunLike.congr_fun h ψ
        exact hψ (neg_eq_zero.mp (hχ _ this))
      have h0 : ∑ ψ : U →+ ZMod N, χ (-ψ u) = 0 := AddChar.sum_eq_zero_of_ne_one this
      rw [h0, zero_smul, zero_smul]
  have h2 : ∀ ψ : U →+ ZMod N, ψ ≠ 0 → ∑ u, χ (-ψ u) = 0 := fun ψ hψ => by
    have : χ.compAddMonoidHom (-ψ) ≠ 1 := by
      intro h
      apply hψ
      ext u
      have := DFunLike.congr_fun h u
      exact neg_eq_zero.mp (hχ _ this)
    exact AddChar.sum_eq_zero_of_ne_one this
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h1]
  rw [← Finset.sum_smul, Finset.sum_comm,
    Finset.sum_eq_single (0 : U →+ ZMod N) (fun ψ _ => h2 ψ) (by simp)]
  simp

theorem sum_ext_char_smul {o M A T : Type} [CommRing o] [IsDomain o] [AddCommGroup M] [Module o M]
    [AddCommGroup A] [AddCommGroup T] [Finite A] [Finite T] {N : ℕ} [NeZero N]
    (i : A →+ T) (p : T →+ A) (hp : ∀ a, p (i a) = a)
    (χ : AddChar (ZMod N) o) (hχ : ∀ a, χ a = 1 → a = 0) (ρ : T → M)
    (hρ : ∀ a u, (∀ ψ : T →+ ZMod N, ψ u = 0) → ρ (i a + u) = ρ (i a)) (c' : A →+ ZMod N) :
    Nat.card T = Nat.card A * Nat.card p.ker ∧
    ∑ᶠ c ∈ {c : T →+ ZMod N | c.comp i = c'}, ∑ᶠ t, χ (-c t) • ρ t
      = (Nat.card p.ker : o) • ∑ᶠ a, χ (-c' a) • ρ (i a) := by
  let q : T →+ p.ker := (AddMonoidHom.id T - i.comp p).codRestrict p.ker fun t => by
    simp [AddMonoidHom.mem_ker, hp]
  have hq : ∀ t, (q t : T) = t - i (p t) := fun t => rfl
  have hqu : ∀ u : p.ker, q u = u := fun u => Subtype.ext (by
    rw [hq, (AddMonoidHom.mem_ker).mp u.2, map_zero, sub_zero])
  have hqi : ∀ a, q (i a) = 0 := fun a => Subtype.ext (by rw [hq, hp, sub_self]; rfl)
  let e : A × p.ker ≃ T :=
    { toFun := fun x => i x.1 + x.2
      invFun := fun t => (p t, q t)
      left_inv := fun x => by
        simp [hp, hqu, hqi, (AddMonoidHom.mem_ker).mp x.2.2]
      right_inv := fun t => by simp [hq] }
  have he : ∀ a (u : p.ker), e (a, u) = i a + u := fun _ _ => rfl
  refine ⟨by rw [← Nat.card_prod, Nat.card_congr e], ?_⟩
  have := Fintype.ofFinite A
  have := Fintype.ofFinite T
  have := Fintype.ofFinite p.ker
  have : Finite (p.ker →+ ZMod N) := DFunLike.finite _
  have := Fintype.ofFinite (p.ker →+ ZMod N)
  have hinj : Function.Injective fun ψ : p.ker →+ ZMod N => c'.comp p + ψ.comp q := by
    intro ψ ψ' h
    ext u
    have := DFunLike.congr_fun (add_left_cancel h) (u : T)
    simpa [hqu] using this
  have hs : {c : T →+ ZMod N | c.comp i = c'}
      = Set.range fun ψ : p.ker →+ ZMod N => c'.comp p + ψ.comp q := by
    ext c
    constructor
    · rintro rfl
      refine ⟨c.comp p.ker.subtype, ?_⟩
      ext t
      simp [hq]
    · rintro ⟨ψ, rfl⟩
      ext a
      simp [hp, hqi]
  rw [hs, finsum_mem_range hinj]
  simp_rw [finsum_eq_sum_of_fintype, ← e.sum_comp, Fintype.sum_prod_type, he]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := sum_char_smul χ hχ (fun u : p.ker => ρ (i a + u)) fun u hu => by
    have := hρ a u fun ψ => hu (ψ.comp p.ker.subtype)
    simpa using this
  simp only [ZeroMemClass.coe_zero, add_zero] at this
  rw [smul_comm, Nat.card_eq_fintype_card, ← this, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_smul, ← AddChar.map_add_eq_mul]
  simp [hp, hqu, hqi, (AddMonoidHom.mem_ker).mp u.2, add_comm]

end GlobalTheory.ThetaProj

namespace GlobalTheory

open ThetaProj

theorem thetaSys_FF_mem_finite_perp_proj :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω),
      (∀ T c k, S.FF T c k ∈ S.R) ∧ Set.Finite {x : Ω | ∃ T c k, x = S.FF T c k} ∧
      (∀ H, S.perp (S.perp H) = H) ∧
      ∀ (T T' : AddSubgroup S.Gam) (h : T' ≤ T), S.IsoFree T → S.IsoFree T' →
        ∀ (c' : T' →+ ZMod S.N), S.proj T' c' =
          ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'}, S.proj T c := by
  intro o Ω _ _ _ hA S
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have : IsDomain o := hA.inj.isDomain _
  refine ⟨fun T c k => ?_, ?_, fun H => ?_, fun T T' h hT hT' c' => ?_⟩
  · have := Fintype.ofFinite T
    rw [ThetaSys.FF, finsum_eq_sum_of_fintype]
    exact S.R.sum_mem fun t _ => S.R.mul_mem (S.R.algebraMap_mem _)
      (S.R.sum_mem fun j _ => S.R.mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))
  · have : Finite (AddSubgroup S.Gam) := Finite.of_injective _ SetLike.coe_injective
    have : ∀ T : AddSubgroup S.Gam, Finite (T →+ ZMod S.N) := fun T => DFunLike.finite _
    refine (Set.finite_range fun x : Σ T : AddSubgroup S.Gam,
      (T →+ ZMod S.N) × (S.J × (T → ZMod ((S.r * S.N) ^ 2))) => S.FF x.1 x.2.1 x.2.2).subset ?_
    rintro x ⟨T, c, k, rfl⟩
    exact ⟨⟨T, c, k⟩, rfl⟩
  · refine le_antisymm (fun x hx => ?_) fun x hx y hy => ?_
    · by_contra hxH
      let H' : Submodule (ZMod (S.r * S.N)) S.Gam := AddSubgroup.toZModSubmodule _ H
      obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := S.r * S.N) (q := H'.mkQ x)
        (fun h0 => hxH ((Submodule.Quotient.mk_eq_zero H').mp h0))
      obtain ⟨b, hb⟩ := exists_eStd_eq _ _ (f ∘ₗ H'.mkQ)
      have hb' : b ∈ S.perp H := fun y hy => by
        rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero H').mpr hy, map_zero]
      have h1 : eStd S.g _ x b = 0 := hx b hb'
      rw [eStd_swap, neg_eq_zero, hb] at h1
      exact hf h1
    · rw [eStd_swap, hy x hx, neg_zero]
  · obtain ⟨d, ⟨e⟩⟩ := hT.2
    obtain ⟨d', ⟨e'⟩⟩ := hT'.2
    obtain ⟨p, hp⟩ := exists_retraction T' e'
    have hζ : IsPrimitiveRoot S.ζN S.N :=
      S.prim.pow (NeZero.pos _) (by ring)
    let χ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hζ.pow_eq_one
    have hχ : ∀ a, χ a = 1 → a = 0 := fun a ha =>
      ((AddChar.zmodChar_primitive_of_primitive_root S.N hζ).zmod_char_eq_one_iff S.N a).mp ha
    let _ : Module (ZMod (S.r * S.N)) T := AddCommGroup.zmodModule fun x => Subtype.ext (by
      rw [AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self,
        zero_smul]
      rfl)
    obtain ⟨h1, h2⟩ := sum_ext_char_smul (AddSubgroup.inclusion h) (p.comp T.subtype)
      (fun a => hp a) χ hχ (fun t : T => S.ρ t) (fun a u hu => by
        have hu' : S.r • (u : S.Gam) = 0 :=
          congrArg Subtype.val (nsmul_eq_zero_of_forall_char (r := S.r) u hu)
        rw [AddSubgroup.coe_add, ← S.ρ_add _ _ (by
          rw [hT.1 (AddSubgroup.inclusion h a).2 u u.2, smul_zero]), S.ρ_one _ hu', _root_.mul_one]) c'
    have hu : IsUnit (Nat.card T : o) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
      exact S.unit.pow _
    have hfin : Finite (T →+ ZMod S.N) := DFunLike.finite _
    have h3 : ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'}, S.proj T c
        = Ring.inverse (Nat.card T : o) •
          ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'},
            ∑ᶠ t : T, χ (-c t) • S.ρ t := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
        finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.smul_sum]
      rfl
    rw [h3, h2, smul_smul]
    rw [h1, Nat.cast_mul] at hu ⊢
    rw [Ring.mul_inverse_rev' (Commute.all _ _), mul_right_comm,
      Ring.inverse_mul_cancel _ (isUnit_of_mul_isUnit_right hu), _root_.one_mul]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterion
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.CosetCrit

theorem posDef_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) : q.PosDef := by
  intro x hx
  by_contra h
  have hinj : Function.Injective fun k : ℤ => k • x := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually_gt_atTop 0
  obtain ⟨k, hk⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul] at hk
  have : (0 : ℝ) ≤ ((k * k : ℤ) : ℝ) := by exact_mod_cast mul_self_nonneg k
  nlinarith [not_lt.1 h]

theorem tendsto_class {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (y : X) {m : ℕ} (hm : m ≠ 0) :
    Filter.Tendsto (fun χ => q (y + m • χ)) Filter.cofinite Filter.atTop := by
  have hinj : Function.Injective fun χ : X => y + m • χ := fun a b h => by
    have h1 : (m : ℤ) • a = (m : ℤ) • b := by simpa using h
    exact smul_right_injective X (by exact_mod_cast hm : (m : ℤ) ≠ 0) h1
  exact hq.comp hinj.tendsto_cofinite

theorem exists_char_pow {C X : Type} [Field C] [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X]
    (t : Multiplicative X →* Cˣ) {k : ℕ} (hk : 0 < k) : ∃ t' : Multiplicative X →* Cˣ, t' ^ k = t := by
  have hroot : ∀ u : Cˣ, ∃ v : Cˣ, v ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : C) hk
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk.ne'] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose r hr using hroot
  let e := Module.Free.chooseBasis ℤ X
  let f : X →ₗ[ℤ] Additive Cˣ :=
    e.constr ℤ fun i => Additive.ofMul (r (t (Multiplicative.ofAdd (e i))))
  have hf : k • f = (MonoidHom.toAdditiveRight t).toIntLinearMap := e.ext fun i => by
    simp only [f, LinearMap.smul_apply, Module.Basis.constr_basis, ← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hf x.toAdd)

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

omit [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] in

theorem norm_txT_le (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) := by
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p χ]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)

omit [CompleteSpace C] [IsAlgClosed C] in

theorem norm_tx_le (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + m • χ₀) ≤ q (p.1.1.toAdd + m • χ)) :
    ‖N.tx m p‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ₀) / (m : ℝ) ^ 2)) := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (Real.exp_pos _).le fun χ => ?_
  refine (norm_txT_le hI hm p χ).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
  exact div_le_div_of_nonneg_right (h₀ χ) (by positivity)

omit [IsUltrametricDist C] [CompleteSpace C] in

theorem exists_lift {n g : ℕ} (hn : (n : C) ≠ 0) (hT : N.Tors n g) (j : ℕ) {t : N.A} (ht : t ^ n = 1) :
    ∃ γ : N.Gt, γ ^ n ^ (j + 1) = 1 ∧ γ.b ^ n ^ j = t := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hn hT j
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  obtain ⟨γ₀, rfl⟩ := h1 t
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ₀ ^ n)).2 (by rw [NumD.Gt.pow_b, ht])
  obtain ⟨s', rfl⟩ := exists_char_pow s hn0
  obtain ⟨γ, hγ⟩ := h2 (γ₀ * (N.tor s')⁻¹)
  refine ⟨γ, ?_, ?_⟩
  · rw [pow_succ, pow_mul, hγ, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
  · rw [← NumD.Gt.pow_b, hγ]
    simp

theorem exists_norm_tx_ge (hI : N.Int q) {n g : ℕ} (hp : n.Prime) (ho : Odd n) (hn : ‖(n : C)‖ = 1)
    (hT : N.Tors n g) {j : ℕ} (hj : 1 ≤ j) (p : N.QT ((n ^ j) ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + n ^ j • χ₀) ≤ q (p.1.1.toAdd + n ^ j • χ)) :
    ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧
      Real.exp (-(q (p.1.1.toAdd + n ^ j • χ₀) / ((n ^ j : ℕ) : ℝ) ^ 2)) ≤ ‖N.tx (n ^ j) (p * h)‖ := by
  have hn0 : (n : C) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hm : Odd (n ^ j) := ho.pow
  have hm0 : 0 < n ^ j := hm.pos
  have hP := posDef_of_tendsto hI.pos
  have hQ : ∀ γ : N.Gt, γ ^ n ^ (j + 1) = 1 → (1, γ) ∈ N.QT ((n ^ j) ^ 2) := fun γ hγ => by
    obtain ⟨c, hc⟩ : n ^ (j + 1) ∣ (n ^ j) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow n (by omega)
    rw [NumD.mem_QT, hc, pow_mul, hγ, one_pow]
    exact N.io_zero.symm
  obtain ⟨t, ht, hth⟩ := hT.good (N.c χ₀ * p.1.2.b ^ n ^ j)
  obtain ⟨γ, hγ, hγb⟩ := exists_lift hn0 hT j ht
  set p₁ : N.QT ((n ^ j) ^ 2) := p * ⟨(1, γ), hQ γ hγ⟩ with hp₁
  have hy : p₁.1.1 = p.1.1 := mul_one _
  have hb : p₁.1.2 = p.1.2 * γ := rfl
  haveI : NeZero (n : C) := ⟨hn0⟩
  haveI : NeZero n := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C n
  have hr : ∀ x : ℝ, Real.exp (-1) ^ x = Real.exp (-x) := fun x => by
    rw [← Real.exp_mul, neg_one_mul]
  have hsq : (0 : ℝ) < ((n ^ j : ℕ) : ℝ) ^ 2 := by positivity
  obtain ⟨s, hs, hle⟩ := GlobalTheory.exists_torsion_twist_tsum_norm_ge C N.X n ζ hp.pos hn hζ
    (N.txT (n ^ j) p₁) (fun χ => q (p.1.1.toAdd + n ^ j • χ) / ((n ^ j : ℕ) : ℝ) ^ 2) (Real.exp (-1))
    (Real.exp_pos _) (by simpa using Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num))
    ((tendsto_class hI.pos _ hm0.ne').atTop_div_const hsq)
    (fun χ => by rw [hr, ← hy]; exact norm_txT_le hI hm p₁ χ) χ₀
    (by rw [hr, (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 _ hm p₁ χ₀, hy, hb, NumD.Gt.mul_b, mul_pow, hγb, ← mul_assoc, hth,
          mul_one])
    (fun μ hμ => by
      refine div_lt_div_of_pos_right ?_ hsq
      have := GlobalTheory.ClassMin.lt_of_min_class_of_ne_zero hP (N := ((n ^ j : ℕ) : ℤ)) (n := (n : ℤ))
        (a := p.1.1.toAdd + n ^ j • χ₀) (by exact_mod_cast hm0.ne') (by exact_mod_cast hp.two_le)
        (fun w => by rw [natCast_zsmul, add_assoc, ← smul_add]; exact h₀ _) hμ
      rwa [mul_comm, mul_smul, natCast_zsmul, natCast_zsmul, add_assoc, ← smul_add] at this)
  obtain ⟨s', rfl⟩ := exists_char_pow s hm0
  have hs' : s' ^ n ^ (j + 1) = 1 := by rw [pow_succ, pow_mul, hs]
  have hγ' : (γ * N.tor s') ^ n ^ (j + 1) = 1 := by
    rw [mul_pow, hγ, ← N.tor_pow, hs', N.tor_one, mul_one]
  refine ⟨⟨(1, γ * N.tor s'), hQ _ hγ'⟩, rfl, hγ', ?_⟩
  set p₂ : N.QT ((n ^ j) ^ 2) := p * ⟨(1, γ * N.tor s'), hQ _ hγ'⟩ with hp₂
  have hone : ∀ x, ‖(s' x : C)‖ = 1 := fun x => by
    have h1 : ‖(s' x : C)‖ ^ n ^ (j + 1) = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hs', MonoidHom.one_apply,
        Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1
  have hterm : ∀ χ, N.txT (n ^ j) p₂ χ =
      ((s' p₁.1.1 : C) ^ (((n ^ j) ^ 2 - 1) / 2) * (s' p₁.1.1 : C)) *
        (N.txT (n ^ j) p₁ χ * ((s' ^ n ^ j) (Multiplicative.ofAdd χ) : C)) := fun χ => by
    rw [(GlobalTheory.T.thetaConstantTerm_representative_dependence C N (n ^ j) hm p₁ p₂ χ).2 s' ((mul_one _).trans hy.symm) (mul_assoc _ _ _).symm,
      ofAdd_add, ofAdd_nsmul, map_mul, map_pow, ofAdd_toAdd, MonoidHom.pow_apply]
    push_cast
    ring
  rw [NumD.tx, funext hterm, tsum_mul_left, norm_mul, norm_mul, norm_pow, hone, one_pow, one_mul, one_mul,
    ← hr]
  exact hle

end GlobalTheory.CosetCrit

theorem GlobalTheory.tx_coset_criterion : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ n g : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n g → ∀ j : ℕ, 1 ≤ j → (∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 ∧ (‖N.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)) ∧ (∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ ‖N.tx (n ^ j) (p * h)‖ = 1) ∧ ∀ p : N.QT ((n ^ j) ^ 2), ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ N.tx (n ^ j) (p * h) ≠ 0 := by
  intro C _ _ _ _ N q hI n g hp ho hn hT j hj
  have hm : Odd (n ^ j) := ho.pow
  have hP := GlobalTheory.CosetCrit.posDef_of_tendsto hI.pos
  have hsq : (0 : ℝ) < ((n ^ j : ℕ) : ℝ) ^ 2 := by have := hm.pos; positivity
  have hmin : ∀ p : N.QT ((n ^ j) ^ 2), ∃ χ₀, ∀ χ,
      q (p.1.1.toAdd + n ^ j • χ₀) ≤ q (p.1.1.toAdd + n ^ j • χ) := fun p =>
    (GlobalTheory.CosetCrit.tendsto_class hI.pos _ hm.pos.ne').exists_forall_le
  have h1 : ∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 := fun p => by
    obtain ⟨χ₀, h₀⟩ := hmin p
    refine (GlobalTheory.CosetCrit.norm_tx_le hI hm p h₀).trans (Real.exp_le_one_iff.2 (neg_nonpos.2 ?_))
    exact div_nonneg (hP.nonneg _) hsq.le
  refine ⟨fun p => ⟨h1 p, fun h => ?_⟩, fun p hp1 => ?_, fun p => ?_⟩
  · obtain ⟨χ₀, h₀⟩ := hmin p
    have h2 := GlobalTheory.CosetCrit.norm_tx_le hI hm p h₀
    rw [h, Real.one_le_exp_iff, neg_nonneg] at h2
    refine ⟨-χ₀, ?_⟩
    rw [smul_neg, eq_neg_iff_add_eq_zero]
    by_contra h3
    exact (div_pos (hP _ h3) hsq).not_ge h2
  · obtain ⟨h, ha, hb, hc⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge hI hp ho hn hT hj p (χ₀ := 0) (fun χ => by
      rw [hp1, toAdd_one, smul_zero, add_zero, map_zero]
      exact hP.nonneg _)
    refine ⟨h, ha, hb, le_antisymm (h1 _) ?_⟩
    simpa [hp1] using hc
  · obtain ⟨χ₀, h₀⟩ := hmin p
    obtain ⟨h, ha, hb, hc⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge hI hp ho hn hT hj p h₀
    exact ⟨h, ha, hb, norm_pos_iff.1 ((Real.exp_pos _).trans_le hc)⟩
end

