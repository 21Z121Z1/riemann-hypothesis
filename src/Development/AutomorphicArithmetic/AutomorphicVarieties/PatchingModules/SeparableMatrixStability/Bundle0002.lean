import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem quot_equiv (K : Type) [Field K] (m : ℕ) :
    Nonempty ((PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) ≃ (Fin m → K)) := by
  let f : PowerSeries K →+ (Fin m → K) :=
    { toFun := fun p i => PowerSeries.coeff (i : ℕ) p
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hs : Function.Surjective f := by
    intro v
    refine ⟨PowerSeries.mk fun i => if h : i < m then v ⟨i, h⟩ else 0, ?_⟩
    ext i
    simp [f]
  have hk : (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}).toAddSubgroup = f.ker := by
    ext p
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff, AddMonoidHom.mem_ker]
    constructor
    · intro h; ext i; exact h i i.2
    · intro h i hi; exact congrFun h ⟨i, hi⟩
  exact ⟨((QuotientAddGroup.quotientAddEquivOfEq hk).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hs)).toEquiv⟩

private theorem l_zero (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] (φ : ℤ_[l] →+* K) : (l : K) = 0 := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite K p
  have hpp : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right hp0
  by_cases hpl : p = l
  · subst hpl
    exact CharP.cast_eq_zero K p
  · exfalso
    have hu : IsUnit (p : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) ?_
      have h1 : ¬ ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        intro hd
        have e := (Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hpp).1 (Int.natCast_dvd_natCast.1 hd)
        exact hpl e.symm
      push_neg at h1
      simpa using h1
    have hu' := hu.map φ
    rw [map_natCast, CharP.cast_eq_zero K p] at hu'
    exact not_isUnit_zero hu'

theorem UpperTheory.V.Pa.am_fin :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m g : ℕ), Finite (x.Am m) ∧ Nat.card (x.Am m) = Nat.card x.K ^ m ∧ IsNilpotent (algebraMap x.A (x.Am m) x.t) ∧ IsNilpotent (algebraMap x.A (DD (x.Am m) g) x.t) ∧ (l : x.A) = 0 ∧ 1 < Nat.card x.K := by
  intro l _ F n x m g
  obtain ⟨e⟩ := quot_equiv x.K m
  have hn : IsNilpotent (algebraMap x.A (x.Am m) x.t) := ⟨m, by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩
  refine ⟨Finite.of_equiv _ e.symm, ?_, hn, hn.map (DD.C : x.Am m →+* DD (x.Am m) g), ?_, Finite.one_lt_card⟩
  · rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
  · have h := l_zero l x.K (algebraMap ℤ_[l] x.K)
    rw [← map_natCast (PowerSeries.C (R := x.K)), h, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocFin
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.coc_fin :
    ∀ (G R : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommRing R] [Finite R] (n : ℕ) (ρ : G → Matrix (Fin n) (Fin n) R), TopFG G → ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g * ρ h) → IsLocallyConstant ρ → {z : G → Matrix (Fin n) (Fin n) R | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹}.Finite := by
  intro G R _ _ _ _ _ n ρ hfg h1 hmul hρ
  obtain ⟨s, hs, hden⟩ := hfg
  haveI : Finite s := hs.to_subtype
  have hinv : ∀ g, ρ g⁻¹ * ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, h1]
  have hinv' : ∀ g, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, h1]
  have hz1 : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → z 1 = 0 := by
    intro z hz
    have := hz 1 1
    simpa [h1] using this
  have hzinv : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) →
      ∀ g, z g⁻¹ = ρ g⁻¹ * (-z g) * ρ g := by
    intro z hz g
    have e := hz g g⁻¹
    rw [mul_inv_cancel, hz1 z hz] at e
    have e2 : ρ g * z g⁻¹ * ρ g⁻¹ = -z g := eq_neg_of_add_eq_zero_right e.symm
    calc z g⁻¹ = ρ g⁻¹ * (ρ g * z g⁻¹ * ρ g⁻¹) * ρ g := by
          simp only [Matrix.mul_assoc]
          rw [hinv, Matrix.mul_one, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = ρ g⁻¹ * (-z g) * ρ g := by rw [e2]
  apply Set.Finite.of_finite_image (f := fun z : G → Matrix (Fin n) (Fin n) R => fun x : s => z x)
    (Set.toFinite _)
  rintro z ⟨hzl, hz⟩ z' ⟨hzl', hz'⟩ he
  let H : Subgroup G :=
    { carrier := {g | z g = z' g}
      mul_mem' := fun {a b} ha hb => by
        change z (a * b) = z' (a * b)
        change z a = z' a at ha
        change z b = z' b at hb
        rw [hz, hz', ha, hb]
      one_mem' := by
        change z 1 = z' 1
        rw [hz1 z hz, hz1 z' hz']
      inv_mem' := fun {a} ha => by
        change z a = z' a at ha
        change z a⁻¹ = z' a⁻¹
        rw [hzinv z hz, hzinv z' hz', ha] }
  have hsH : Subgroup.closure s ≤ H := (Subgroup.closure_le H).2 fun x hx => congrFun he ⟨x, hx⟩
  have hcl : IsClosed (H : Set G) := by
    have hd := hzl.comp₂ hzl' (fun a b => a - b)
    have hc := hd.isClosed_fiber 0
    convert hc using 1
    ext g
    exact sub_eq_zero.symm
  have hU : (H : Set G) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hden.closure_eq]
    exact closure_minimal (fun x hx => hsH hx) hcl
  funext g
  have hg : g ∈ (H : Set G) := hU ▸ Set.mem_univ g
  exact hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocKer
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem closed_zero {Γ K : Type} [TopologicalSpace Γ] [Field K] {f : Γ → PowerSeries K}
    (hf : AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) f) : IsClosed {g | f g = 0} := by
  have hset : {g | f g = 0} = ⋂ N : ℕ,
      {g | Ideal.Quotient.mk ((Ideal.span {(PowerSeries.X : PowerSeries K)}) ^ N) (f g) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · intro h N
      rw [h]
      exact dvd_zero _
    · intro h
      ext n
      have := (PowerSeries.X_pow_dvd_iff).1 (h (n + 1)) n (Nat.lt_succ_self n)
      simpa using this
  rw [hset]
  exact isClosed_iInter fun N => (hf N).isClosed_fiber 0

theorem UpperTheory.V.Pa.coc_ker :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (s : Set G.G₀) (z : G.G₀ → Matrix (Fin n) (Fin n) x.A), h.p.ker ≤ (Subgroup.normalClosure (Subtype.val '' s)).topologicalClosure → (∀ a ∈ s, h.p₀ a = 1 ∧ z a = 0) → z ∈ SelM h x x.A → ∃ y : G0.G₀ → Matrix (Fin n) (Fin n) x.A, ∀ g, y (h.p₀ g) = z g := by
  intro l _ L G G0 h n x s z hker hs hz
  obtain ⟨-, hcont, hcoc, hconj, -, -⟩ := hz
  have coc : ∀ g k : G.G₀,
      z (g * k) = z g + x.ρX x.A (h.p₀ g) * z k * x.ρX x.A (h.p₀ g⁻¹) := hcoc
  have hρ1 : ∀ g : G.G₀, h.p₀ g = 1 → x.ρX x.A (h.p₀ g) = 1 := by
    intro g hg
    rw [hg]
    simp [NP.ρX]
  have hz1 : z 1 = 0 := by
    have e := coc 1 1
    rw [hρ1 1 (map_one _), inv_one, hρ1 1 (map_one _), one_mul, mul_one] at e
    simpa using e
  have hR : ∀ g k : G.G₀, z k = 0 → z (g * k) = z g := by
    intro g k hk
    rw [coc, hk]
    simp
  let H : Subgroup G.G₀ :=
    { carrier := {k | h.p₀ k = 1 ∧ z k = 0}
      one_mem' := ⟨map_one _, hz1⟩
      mul_mem' := by
        rintro a b ⟨ha, za⟩ ⟨hb, zb⟩
        refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
        rw [hR a b zb, za]
      inv_mem' := by
        rintro a ⟨ha, za⟩
        refine ⟨by rw [map_inv, ha, inv_one], ?_⟩
        have e := hR a⁻¹ a za
        rw [inv_mul_cancel, hz1] at e
        exact e.symm }
  have hHconj : ∀ g k : G.G₀, k ∈ H → g * k * g⁻¹ ∈ H := by
    rintro g k ⟨hk1, hk2⟩
    refine ⟨by rw [map_mul, map_mul, hk1, mul_one, map_inv, mul_inv_cancel], ?_⟩
    have hkg : z (k * g⁻¹) = z g⁻¹ := by
      rw [coc, hk2, hρ1 k hk1]
      have : h.p₀ k⁻¹ = 1 := by rw [map_inv, hk1, inv_one]
      rw [hρ1 _ this]
      simp
    rw [mul_assoc, coc, hkg, ← coc, mul_inv_cancel, hz1]
  have hHc : ∀ k : G.G₀, k ∈ H → G.frame.conj k ∈ H := by
    rintro k ⟨hk1, hk2⟩
    refine ⟨?_, ?_⟩
    · rw [h.p₀_conj, hk1, map_one]
    · rw [hconj, hk2]
      simp
  let N : Subgroup G.Γ := H.map G.η.ker.subtype
  have hN : N.Normal := by
    constructor
    intro m hm γ
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hm
    rcases Int.units_eq_one_or (G.η γ) with hγ | hγ
    · have e : γ * (k : G.Γ) * γ⁻¹ = (((⟨γ, hγ⟩ : G.G₀) * k * (⟨γ, hγ⟩ : G.G₀)⁻¹ : G.G₀) : G.Γ) := rfl
      exact Subgroup.mem_map.2 ⟨_, hHconj _ _ hk, e.symm⟩
    · have hg : G.c⁻¹ * γ ∈ G.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, G.η_c, hγ]
        rfl
      let g : G.G₀ := ⟨G.c⁻¹ * γ, hg⟩
      have e : γ * (k : G.Γ) * γ⁻¹ = ((G.frame.conj (g * k * g⁻¹) : G.G₀) : G.Γ) := by
        show γ * (k : G.Γ) * γ⁻¹ = G.c * ((G.c⁻¹ * γ) * (k : G.Γ) * (G.c⁻¹ * γ)⁻¹) * G.c⁻¹
        group
      exact Subgroup.mem_map.2 ⟨_, hHc _ (hHconj _ _ hk), e.symm⟩
  have hHclosed : IsClosed (H : Set G.G₀) := by
    have e1 : (H : Set G.G₀) = {k | h.p₀ k = 1} ∩ ⋂ i, ⋂ j, {k | z k i j = 0} := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i j => by rw [h2]; rfl⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Matrix.ext fun i j => h2 i j⟩
    rw [e1]
    exact IsClosed.inter ((isClosed_singleton (x := (1 : G0.G₀))).preimage h.p₀_cont)
      (isClosed_iInter fun i => isClosed_iInter fun j => closed_zero (hcont i j))
  have hNclosed : IsClosed (N : Set G.Γ) := by
    show IsClosed (Subtype.val '' (H : Set G.G₀))
    exact hHclosed.trans (Subgroup.isClosed_of_isOpen _ G.η_open)
  have hsN : Subtype.val '' s ⊆ (N : Set G.Γ) := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.2 ⟨a, ⟨(hs a ha).1, (hs a ha).2⟩, rfl⟩
  have hkerN : h.p.ker ≤ N :=
    hker.trans (Subgroup.topologicalClosure_minimal _
      (Subgroup.normalClosure_le_normal (N := N) hsN) hNclosed)
  have hfac : ∀ g g' : G.G₀, h.p₀ g = h.p₀ g' → z g = z g' := by
    intro g g' e
    have h1 : h.p₀ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
    have h2 : ((g⁻¹ * g' : G.G₀) : G.Γ) ∈ h.p.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
    obtain ⟨k, hk, hk'⟩ := Subgroup.mem_map.1 (hkerN h2)
    have hkk : k = g⁻¹ * g' := Subtype.ext hk'
    rw [hkk] at hk
    have e2 := hR g _ hk.2
    rw [mul_inv_cancel_left] at e2
    exact e2.symm
  exact ⟨fun g0 => z (Classical.choose (h.p₀_surj g0)),
    fun g => hfac _ _ (Classical.choose_spec (h.p₀_surj (h.p₀ g)))⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocPl
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Abs

variable {K M : Type} [Group K] [Ring M] (ρ z : K → M) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
  (hz : ∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹)

include h1 hz in
private theorem cocycle_apply_one_eq_zero : z 1 = 0 := by
  simpa [h1] using hz 1 1

include h1 hm in
private theorem cp_inv {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem cp_add {g : K} (hg : ρ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, hg, cp_inv ρ h1 hm hg, one_mul, mul_one]

include h1 hm hz in
private theorem cp_pow {g : K} (hg : ρ g = 1) (k : ℕ) : ρ (g ^ k) = 1 ∧ z (g ^ k) = k • z g := by
  induction k with
  | zero => exact ⟨by simpa using h1, by simpa using cocycle_apply_one_eq_zero ρ z h1 hz⟩
  | succ k ih =>
    refine ⟨by rw [pow_succ', hm, hg, ih.1, one_mul], ?_⟩
    rw [pow_succ', cp_add ρ z h1 hm hz hg, ih.2, succ_nsmul']

include h1 hm hz in
private theorem cp_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ z g = 0 := by
  have hinv : ∀ g, ρ g = 1 → z g = 0 → ρ g⁻¹ = 1 ∧ z g⁻¹ = 0 := by
    intro g hg hzg
    refine ⟨cp_inv ρ h1 hm hg, ?_⟩
    have := cp_add ρ z h1 hm hz hg g⁻¹
    rwa [mul_inv_cancel, cocycle_apply_one_eq_zero ρ z h1 hz, hzg, zero_add, eq_comm] at this
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ z g = 0}
      mul_mem' := by
        rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
        exact ⟨by rw [hm, ha, hb, one_mul], by rw [cp_add ρ z h1 hm hz ha, hza, hzb, zero_add]⟩
      one_mem' := ⟨h1, cocycle_apply_one_eq_zero ρ z h1 hz⟩
      inv_mem' := by
        rintro a ⟨ha, hza⟩
        exact hinv a ha hza }
  have hS : IsOpen (S : Set K) := (cρ.isOpen_fiber 1).inter (cz.isOpen_fiber 0)
  have hN : S.Normal := by
    constructor
    rintro a ⟨ha, hza⟩ k
    show ρ (k * a * k⁻¹) = 1 ∧ z (k * a * k⁻¹) = 0
    refine ⟨?_, ?_⟩
    · rw [hm, hm, ha, mul_one, ← hm, mul_inv_cancel, h1]
    · rw [mul_assoc, hz, cp_add ρ z h1 hm hz ha, hza, zero_add, ← hz, mul_inv_cancel, cocycle_apply_one_eq_zero ρ z h1 hz]
  exact ⟨{ toOpenSubgroup := ⟨S, hS⟩, isNormal' := hN }, fun g => Iff.rfl⟩

end Abs

private theorem cp_lc {K R : Type} [TopologicalSpace K] [CommRing R] {n : ℕ} (I : Ideal R)
    (f : K → Matrix (Fin n) (Fin n) R) (hf : ∀ i j, AdicCont I fun g => f g i j) (m : ℕ) :
    IsLocallyConstant fun g => (Ideal.Quotient.mk (I ^ m)).mapMatrix (f g) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  have e : (fun g => (Ideal.Quotient.mk (I ^ m)).mapMatrix (f g)) ⁻¹' {y} =
      ⋂ i, ⋂ j, (fun g => Ideal.Quotient.mk (I ^ m) (f g i j)) ⁻¹' {y i j} := by
    ext g
    simp [← Matrix.ext_iff]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hf i j m).isOpen_fiber _

private theorem cp_zero {R : Type} [CommRing R] {n : ℕ} (J : Ideal R) (A : Matrix (Fin n) (Fin n) R) :
    (Ideal.Quotient.mk J).mapMatrix A = 0 ↔ ∀ i j, A i j ∈ J := by
  rw [← Matrix.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

private theorem cp_one {R : Type} [CommRing R] {n : ℕ} (J : Ideal R) (A : Matrix (Fin n) (Fin n) R) :
    (Ideal.Quotient.mk J).mapMatrix A = 1 ↔ ∀ i j, (A - 1) i j ∈ J := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J).mapMatrix, ← map_sub, cp_zero]

theorem UpperTheory.V.Pa.coc_pl :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (n : ℕ) (R : Type) [CommRing R] (I : Ideal R) (ρ z : G.G₀ → Matrix (Fin n) (Fin n) R) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (l : R) = 0 → ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g * ρ h) → (∀ i j, AdicCont I fun g => ρ g i j) → (∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m) → (∀ i j, AdicCont I fun g => z g i j) → (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → (∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m) ∧ ∀ k : G.G₀, (k : G.Γ) ∈ PL l H → ∀ (m : ℕ) i j, (ρ k - 1) i j ∈ I ^ m ∧ z k i j ∈ I ^ m := by
  intro l _ L G n R _ I ρ z H _ hHo hHk hl h1 hm hρc hρH hzc hz
  have main : ∀ m : ℕ, (∀ (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j,
      (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m) ∧
      ∀ k : G.G₀, (k : G.Γ) ∈ PL l H → ∀ i j, (ρ k - 1) i j ∈ I ^ m ∧ z k i j ∈ I ^ m := by
    intro m
    let ρ' := fun x => (Ideal.Quotient.mk (I ^ m)).mapMatrix (ρ x)
    let z' := fun x => (Ideal.Quotient.mk (I ^ m)).mapMatrix (z x)
    have h1' : ρ' 1 = 1 := by simp [ρ', h1]
    have hm' : ∀ a b, ρ' (a * b) = ρ' a * ρ' b := by
      intro a b
      simp [ρ', hm]
    have hz' : ∀ a b, z' (a * b) = z' a + ρ' a * z' b * ρ' a⁻¹ := by
      intro a b
      simp only [z', ρ', hz, map_add, map_mul]
    have hlq : ((l : ℕ) : R ⧸ I ^ m) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (I ^ m)), hl, map_zero]
    have key : ∀ g : G.G₀, ρ' g = 1 → ρ' (g ^ l) = 1 ∧ z' (g ^ l) = 0 := by
      intro g hg
      obtain ⟨p1, p2⟩ := cp_pow ρ' z' h1' hm' hz' hg l
      refine ⟨p1, p2.trans ?_⟩
      ext i j
      simp [Matrix.smul_apply, nsmul_eq_mul, hlq]
    have P1 : ∀ (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j,
        (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m := by
      intro h hh
      obtain ⟨e, he⟩ := hρH m h hh
      refine ⟨e + 1, fun i j => ?_⟩
      rw [pow_succ l e, pow_mul]
      obtain ⟨q1, q2⟩ := key _ ((cp_one _ _).2 he)
      exact ⟨(cp_one _ _).1 q1 i j, (cp_zero _ _).1 q2 i j⟩
    refine ⟨P1, ?_⟩
    obtain ⟨U, hU⟩ := cp_U ρ' z' h1' hm' hz' (cp_lc I ρ hρc m) (cp_lc I z hzc m)
    intro k hk i j
    have hkU : k ∈ U := by
      refine pl_sub l G.Γ H G.η.ker G.η_open hHk U ?_ k hk
      intro h hh
      obtain ⟨e, he⟩ := P1 h hh
      exact ⟨e, (hU _).2 ⟨(cp_one _ _).2 fun i j => (he i j).1, (cp_zero _ _).2 fun i j => (he i j).2⟩⟩
    obtain ⟨q1, q2⟩ := (hU k).1 hkU
    exact ⟨(cp_one _ _).1 q1 i j, (cp_zero _ _).1 q2 i j⟩
  exact ⟨fun m h hh => (main m).1 h hh, fun k hk m i j => (main m).2 k hk i j⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem md_comm {A B G G' : Type} [CommRing A] [CommRing B] [Group G] [Group G'] (f : G →* G')
    (φ : A →+ B) (y : MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.map φ y) =
      MonoidAlgebra.map φ (MonoidAlgebra.mapDomainRingHom A f y) := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply]
  apply MonoidAlgebra.coeff_injective
  simp only [MonoidAlgebra.coeff_map, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_mapRange _ _ _ _ (map_add φ)

private theorem md_comm' {A B G G' : Type} [CommRing A] [CommRing B] [Group G] [Group G'] (f : G →* G')
    (φ : A →+* B) (y : MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.mapRingHom G φ y) =
      MonoidAlgebra.mapRingHom G' φ (MonoidAlgebra.mapDomainRingHom A f y) := by
  exact md_comm f φ.toAddMonoidHom y

private theorem md_surj (A : Type) {G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) : Function.Surjective (MonoidAlgebra.mapDomainRingHom A f) := by
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hf y.coeff
  refine ⟨MonoidAlgebra.ofCoeff x, ?_⟩
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain, MonoidAlgebra.coeff_ofCoeff, hx]

private theorem comap_chi {n : ℕ} {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G')
    (y : MonoidAlgebra A G) : (D.comap f).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A f y) := by
  show D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom _ f
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C y)) = _
  rw [map_sub, md_comm', MonoidAlgebra.mapDomainRingHom_apply (Polynomial A) f (MonoidAlgebra.single 1 Polynomial.X),
    MonoidAlgebra.mapDomain_single, map_one]
  rfl

private theorem md_gen {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') {m : ℕ}
    (y : Fin m → MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom _ f (GDet.gen y) = GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j) := by
  unfold GDet.gen
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_smul,
    ← MonoidAlgebra.mapDomainRingHom_apply, md_comm']

private theorem mem_CH {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (z : MonoidAlgebra A G) :
    z ∈ D.CH ↔ ∃ (m : ℕ) (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ),
      z = MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β) (Polynomial.aeval (GDet.gen y)
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y))) := by
  simp only [GDet.CH, Set.mem_setOf_eq]
  refine exists_congr fun m => exists_congr fun y => exists_congr fun β => ?_
  constructor
  · intro h
    apply MonoidAlgebra.coeff_injective
    ext g
    rw [h g, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
    rfl
  · intro h g
    rw [h, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
    rfl

private theorem md_CH {n : ℕ} {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G')
    {m : ℕ} (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ) :
    MonoidAlgebra.mapDomainRingHom A f (MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β)
      (Polynomial.aeval (GDet.gen y)
        (((D.comap f).map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y)))) =
    MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β)
      (Polynomial.aeval (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j))
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi
          (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j)))) := by
  rw [md_comm]
  congr 1
  have hc : ((D.comap f).map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y) =
      (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi
        (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j)) := by
    rw [← md_gen]
    exact comap_chi f (D.map MvPolynomial.C) (GDet.gen y)
  rw [hc, ← md_gen]
  exact (Polynomial.aeval_algHom_apply
    (MonoidAlgebra.mapDomainAlgHom (R := MvPolynomial (Fin m) A) (A := MvPolynomial (Fin m) A) f) _ _).symm

theorem UpperTheory.V.Pa.comap_lam :
    ∀ (n : ℕ) (A G G' : Type) [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G'), (∀ y, (D.comap f).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ i y, (D.comap f).lam i y = D.lam i (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ y, (D.comap f).tr y = D.tr (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ (B : Type) [CommRing B] (φ : A →+* B), (D.comap f).map φ = (D.map φ).comap f) ∧ (∀ ρ : G' →* Matrix (Fin n) (Fin n) A, (GDet.ofRep ρ).comap f = GDet.ofRep (ρ.comp f)) ∧ (Function.Surjective f → (∀ D' : GDet n A G', D'.comap f = D.comap f → D' = D) ∧ MonoidAlgebra.mapDomainRingHom A f '' (D.comap f).CH = D.CH) := by
  intro n A G G' _ _ _ f D
  refine ⟨comap_chi f D, ?_, ?_, ?_, ?_, ?_⟩
  · intro i y
    simp only [GDet.lam, comap_chi]
  · intro y
    simp only [GDet.tr, GDet.lam, comap_chi]
  · intro B _ φ
    apply GDet.ext
    intro C _ _ x
    rfl
  · intro ρ
    apply GDet.ext
    intro B _ _ x
    have key : ((GDet.repAlg ρ B).comp (MonoidAlgebra.mapDomainAlgHom (R := B) (A := B) f)) =
        GDet.repAlg (ρ.comp f) B := by
      apply MonoidAlgebra.algHom_ext
      · intro g
        simp [GDet.repAlg, MonoidAlgebra.mapDomainAlgHom]
      · exact Subsingleton.elim _ _
    show Matrix.det (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B f x)) =
      Matrix.det (GDet.repAlg (ρ.comp f) B x)
    rw [← key]
    rfl
  · intro hf
    constructor
    · intro D' h
      apply GDet.ext
      intro B _ _ x
      obtain ⟨x', rfl⟩ := md_surj B f hf x
      exact congrArg (fun E : GDet n A G => E.D B x') h
    · ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨m, y, β, rfl⟩ := (mem_CH _ _).1 hw
        exact (mem_CH _ _).2 ⟨m, _, β, md_CH f D y β⟩
      · intro hz
        obtain ⟨m, y', β, rfl⟩ := (mem_CH _ _).1 hz
        choose y hy using fun j => md_surj A f hf (y' j)
        have hy' : (fun j => MonoidAlgebra.mapDomainRingHom A f (y j)) = y' := funext hy
        refine ⟨_, (mem_CH _ _).2 ⟨m, y, β, rfl⟩, ?_⟩
        rw [md_CH, hy']
end

