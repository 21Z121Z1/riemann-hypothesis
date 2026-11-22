import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryDoubleCosetIndicator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryDoubleCosetIndicatorAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkKValLt
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem okK_val_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ)
    (ht : valuation k (t : k) < valuation k (unif k : k) ^ 2) : valuation k (t : k) < 1 := by
  have hw : valuation k (unif k : k) < 1 := by
    rw [GlAx.unif_spec]
    exact uniformizer_lt_one
  exact ht.trans (pow_lt_one₀ zero_le' hw two_ne_zero)

private theorem okK_conj {k : Type} [Field k] (g₀ : GL (Fin 2) k) (a b : kˣ) :
    ((g₀ * diagT k (Fin 2) ![a, b] * g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (a : k) + b ∧
    ((g₀ * diagT k (Fin 2) ![a, b] * g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (a : k) * b := by
  have hinv : ((g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g₀ : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_diagT]
  constructor
  · rw [Matrix.trace_mul_cycle, hinv, one_mul]
    simp [Matrix.trace_diagonal, Fin.sum_univ_two]
  · rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hinv,
      Matrix.det_one, one_mul]
    simp [Matrix.det_diagonal, Fin.prod_univ_two]

theorem UpperTheory.V.Z.Sym.Sig.okK :
    UpperTheory.V.Z.Sym.Sig.OkK := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ t ht S
  have htv : valuation k (t : k) < 1 := okK_val_lt k t ht
  have hSD : SDom (![t, 1] : Fin 2 → kˣ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    simpa using htv
  have hχH : ∀ u ∈ V.H, χ u = 1 := fun u hu => hχ u (V.H_le hu)
  obtain ⟨_, hZJ, hZd⟩ := eqZ k V χ hχH 2 two_pos
  obtain ⟨_, hmul, hJJ, hfin⟩ := hZd ![t, 1] hSD
  obtain ⟨_, _, _, hIsScal, hmt, hcomap⟩ := eD_facts k O hO h2 Δ s hs hs0
  have hfK : ∀ g, S.fK t g = (((χ t)⁻¹ : ℂˣ) : ℂ) * V.fZ χ ![t, 1] (eD hs g) := fun g => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro u hu y
    have hu' : eD hs u ∈ V.J 2 := hu
    constructor
    · rw [hfK, hfK, map_mul]
      have e := hJJ (eD hs u) hu' 1 (Subgroup.one_mem _) (eD hs y)
      rw [mul_one] at e
      rw [e]
    · rw [hfK, hfK, map_mul]
      have e := hJJ 1 (Subgroup.one_mem _) (eD hs u) hu' (eD hs y)
      rw [one_mul] at e
      rw [e]
  · intro z s' hz y
    rw [hfK, hfK, map_mul, (hIsScal z s').mp hz, hmul]
    ring
  · have hcj : Subgroup.comap (eD hs) (V.ZJ 2) = ZD Δ ⊔ S.J2 := hcomap V
    have hright : ∀ (g w : GL (Fin 2) k), w ∈ V.ZJ 2 →
        (V.fZ χ ![t, 1] (g * w) ≠ 0 ↔ V.fZ χ ![t, 1] g ≠ 0) := by
      intro g w hw
      obtain ⟨z, j, hj, rfl⟩ := (hZJ w).mp hw
      have hc : g * GeneralLinearGroup.scalar (Fin 2) z = GeneralLinearGroup.scalar (Fin 2) z * g := by
        apply Units.ext
        simp only [Units.val_mul, GeneralLinearGroup.coe_scalar]
        exact (scalar_commute (z : k) (fun r => Commute.all _ r) (g : Matrix (Fin 2) (Fin 2) k)).eq.symm
      have e := hJJ 1 (Subgroup.one_mem _) j hj g
      rw [one_mul] at e
      rw [← mul_assoc, hc, mul_assoc, hmul, e]
      exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (Units.ne_zero _) h⟩
    let φ : (DX Δ ⧸ (ZD Δ ⊔ S.J2)) → (GL (Fin 2) k ⧸ V.ZJ 2) :=
      fun x => (QuotientGroup.mk (eD hs x.out))
    have hφ : ∀ x x', φ x = φ x' → x = x' := by
      intro x x' he
      have hm := QuotientGroup.eq.mp he
      rw [← map_inv, ← map_mul, ← Subgroup.mem_comap, hcj] at hm
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
      exact QuotientGroup.eq.mpr hm
    refine (Set.Finite.preimage (f := φ) (fun x _ x' _ he => hφ x x' he) hfin).subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
    rw [hfK] at hx
    have hx' := right_ne_zero_of_mul hx
    show V.fZ χ ![t, 1] (Quotient.out (QuotientGroup.mk (eD hs x.out) : GL (Fin 2) k ⧸ V.ZJ 2)) ≠ 0
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (V.ZJ 2) (eD hs x.out)
    rw [hw, hright _ _ w.2]
    exact hx'
  · intro g hg
    rw [hfK] at hg
    have hg' : V.fZ χ ![t, 1] (eD hs g) ≠ 0 := right_ne_zero_of_mul hg
    obtain ⟨g₀, a, b, hgeq, hab⟩ := suppZ k V χ ![t, 1] hSD (eD hs g) hg'
    have ha := a.ne_zero
    have hb := b.ne_zero
    refine ⟨((a / b : kˣ) : k) + ((a / b : kˣ)⁻¹ : kˣ), ⟨a / b / t, ?_, ?_⟩, ?_⟩
    · exact (by simpa using hab : a / b / t ∈ V.H)
    · have e : t * (a / b / t) = a / b := by rw [mul_comm, div_mul_cancel]
      rw [e]
    · obtain ⟨hdet, htr⟩ := hmt g
      rw [show dg ![a, b] = diagT k (Fin 2) ![a, b] from rfl] at hgeq
      obtain ⟨htr', hdet'⟩ := okK_conj g₀ a b
      rw [hdet, htr, hgeq, htr', hdet', ← map_pow, ← map_mul]
      congr 1
      simp only [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, inv_div]
      field_simp
      ring

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScalarComm
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym

namespace UpperTheory.V.Z.Sym.Sig

section Abs

open MulAction

private theorem one_orbit {T Y : Type} [Group T] [MulAction T Y] (C S : Subgroup T) (f : Y → ℂ) (y₀ : Y) (c : ℂ)
    (P : Prop) [Decidable P] (hs : ∀ y, f y ≠ 0 → P ∧ y ∈ orbit T y₀) (hv : P → ∀ y ∈ orbit T y₀, f y = c)
    (ht : ∀ y ∈ orbit T y₀, stabilizer T y = S) :
    {o : orbitRel.Quotient T Y | f o.out ≠ 0}.Finite ∧
      wcount C f = if P then (S.relIndex C : ℂ) * c else 0 := by
  have key : ∀ o : orbitRel.Quotient T Y, f o.out ≠ 0 → o = Quotient.mk'' y₀ := fun o ho =>
    (Quotient.out_eq' o).symm.trans (Quotient.eq''.2 (hs _ ho).2)
  refine ⟨Set.Subsingleton.finite fun o ho o' ho' => (key o ho).trans (key o' ho').symm, ?_⟩
  unfold wcount
  by_cases hP : P
  · rw [if_pos hP, finsum_eq_single _ (Quotient.mk'' y₀)]
    · have hm : (Quotient.mk'' y₀ : orbitRel.Quotient T Y).out ∈ orbit T y₀ :=
        orbitRel_apply.1 (Quotient.eq''.1 (Quotient.out_eq' _))
      rw [ht _ hm, hv hP _ hm]
    · intro o ho
      have h0 : f o.out = 0 := by_contra fun h => ho (key o h)
      simp [h0]
  · rw [if_neg hP]
    have h0 : ∀ o : orbitRel.Quotient T Y, f o.out = 0 := fun o => by_contra fun h => hP (hs _ h).1
    simp [h0]

end Abs

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem scalar_eq {n : ℕ} (z : kˣ) : GeneralLinearGroup.scalar (Fin n) z = dg (fun _ => z) := by
  apply Units.ext
  ext i j
  simp [val_diagT, Matrix.diagonal_apply, Matrix.one_apply, GeneralLinearGroup.scalar]

private theorem scalar_comm {n : ℕ} (z : kˣ) (x : GL (Fin n) k) :
    GeneralLinearGroup.scalar (Fin n) z * x = x * GeneralLinearGroup.scalar (Fin n) z := by
  apply Units.ext
  ext i j
  simp [GeneralLinearGroup.scalar, mul_comm]

private theorem conj_sc {G : Type} [Group G] (S j W : G) (h : S * j⁻¹ = j⁻¹ * S) :
    S * (j⁻¹ * W * j) = j⁻¹ * S * W * j := by
  rw [← mul_assoc, ← mul_assoc, h]

private theorem dg_mul {n : ℕ} (a b : Fin n → kˣ) : dg (a * b) = dg a * dg b := map_mul _ _ _

private theorem dg_inv {n : ℕ} (a : Fin n → kˣ) : dg a⁻¹ = (dg a)⁻¹ := map_inv _ _

private theorem dg_comm {n : ℕ} (a b : Fin n → kˣ) : dg a * dg b = dg b * dg a := by
  rw [← dg_mul, ← dg_mul, mul_comm]

private theorem sdom2 {x : Fin 2 → kˣ} (h : valuation k (x 0 : k) < valuation k (x 1 : k)) : SDom x := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact h | exact absurd hij (by decide)

private theorem dg_mem_ZJ (V : Lev k) (ω : kˣ →* ℂˣ) (hω : ∀ u ∈ V.H, ω u = 1) {w : Fin 2 → kˣ} :
    dg w ∈ V.ZJ 2 ↔ w 0 / w 1 ∈ V.H := by
  have hz := (eqZ k V ω hω 2 (by norm_num)).2.1
  constructor
  · intro h
    obtain ⟨z, j, hj, e⟩ := (hz _).1 h
    have e1 : dg w = dg (fun _ => z) * j := by rw [e, scalar_eq]
    have e2 : j = dg ((fun _ => z)⁻¹ * w) := by
      rw [dg_mul, dg_inv, e1, inv_mul_cancel_left]
    have hm : ∀ i, ((fun _ => z)⁻¹ * w : Fin 2 → kˣ) i ∈ V.H := by
      intro i
      obtain ⟨u, hu, hu'⟩ := ((memJ k V 2 j).1 hj).2.2 i
      have : u = ((fun _ => z)⁻¹ * w : Fin 2 → kˣ) i := by
        apply Units.ext
        rw [hu', e2, dg, val_diagT, diagonal_apply_eq]
      exact this ▸ hu
    have := div_mem (hm 0) (hm 1)
    simpa [mul_div_mul_left_eq_div] using this
  · intro h
    refine (hz _).2 ⟨w 1, dg ![w 0 / w 1, 1], V.dg_mem ?_, ?_⟩
    · intro i
      fin_cases i
      · exact h
      · exact one_mem _
    · rw [scalar_eq, ← dg_mul]
      congr 1
      funext i
      fin_cases i <;> simp

private theorem supp_orb (V : Lev k) (ω : kˣ →* ℂˣ) (d : Fin 2 → kˣ) (hd : SDom d) (g₀ : GL (Fin 2) k) (a b : kˣ)
    (hab : valuation k (a : k) < valuation k (b : k)) (g : GL (Fin 2) k)
    (h : V.fZ ω d (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g) ≠ 0) :
    a / b / (d 0 / d 1) ∈ V.H ∧ ∃ u : Fin 2 → kˣ, ∃ j ∈ V.J 2, g = g₀ * dg u * j := by
  have hex : ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g) ∈ V.DC d := by
    by_contra hn
    exact h (by rw [Lev.fZ, dif_neg hn])
  obtain ⟨z, hz⟩ := hex
  obtain ⟨j, hj, s, ⟨s', hs', rfl⟩, e⟩ := contract k V 2 (MonoidHom.id _) (pres_id V 2) d hd _ hz
  have hs : ∀ i, s' i ∈ V.H := fun i => hs' i trivial
  have e' : j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g)) * j = dg s' * dg d := e
  have hc := scalar_comm z j⁻¹
  have e3 : (g₀⁻¹ * g * j)⁻¹ * dg ![a, b] * (g₀⁻¹ * g * j) = dg ((fun _ => z) * s' * d) := by
    rw [dg_mul, dg_mul, mul_assoc (dg fun _ => z), ← e', ← scalar_eq, conj_sc _ _ _ hc]
    group
  have hv : ∀ i, valuation k (s' i : k) = 1 := fun i => V.H_le (hs i)
  have hzpos : 0 < valuation k (z : k) := zero_lt_iff.2 (by simp)
  have hsd : SDom ((fun _ => z) * s' * d) := sdom2 (by
    simp only [Pi.mul_apply, Units.val_mul, map_mul, hv, mul_one]
    exact mul_lt_mul_of_pos_left (hd 0 1 (by decide)) hzpos)
  obtain ⟨E, u, hu⟩ := conjDiag k 2 ![a, b] _ (sdom2 hab) hsd _ e3
  have ha : a = z * s' 0 * d 0 := congrFun E 0
  have hb : b = z * s' 1 * d 1 := congrFun E 1
  refine ⟨?_, u, j⁻¹, inv_mem hj, ?_⟩
  · have : a / b / (d 0 / d 1) = s' 0 / s' 1 := by
      rw [ha, hb, mul_assoc z, mul_assoc z, mul_div_mul_left_eq_div, mul_div_mul_comm, mul_div_cancel_right]
    rw [this]
    exact div_mem (hs 0) (hs 1)
  · rw [← hu]
    group

private theorem value_orb (V : Lev k) (ω : kˣ →* ℂˣ) (hω : ∀ u ∈ V.H, ω u = 1) (d : Fin 2 → kˣ) (hd : SDom d)
    (g₀ : GL (Fin 2) k) (a b : kˣ) (hc : a / b / (d 0 / d 1) ∈ V.H) (u : Fin 2 → kˣ) (v : GL (Fin 2) k)
    (hv : v ∈ V.ZJ 2) :
    V.fZ ω d ((g₀ * dg u * v)⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * (g₀ * dg u * v)) = (ω (d 1 / b) : ℂ) := by
  have hE := eqZ k V ω hω 2 (by norm_num)
  obtain ⟨z', j, hj, rfl⟩ := (hE.2.1 v).1 hv
  have hD : dg ![a, b] = GeneralLinearGroup.scalar (Fin 2) (b / d 1) * (dg ![a / b / (d 0 / d 1), 1] * dg d) := by
    rw [scalar_eq, ← dg_mul, ← dg_mul]
    congr 1
    funext i
    fin_cases i
    · apply Units.ext
      simp
      field_simp
    · simp
  have hX : (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j))⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) *
      (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j)) =
      GeneralLinearGroup.scalar (Fin 2) (b / d 1) * (j⁻¹ * dg ![a / b / (d 0 / d 1), 1] * dg d * j) := by
    have h1 : (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j))⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) *
        (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j)) =
        j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z')⁻¹ * ((dg u)⁻¹ * dg ![a, b] * dg u) *
          GeneralLinearGroup.scalar (Fin 2) z') * j := by group
    have h2 : (dg u)⁻¹ * dg ![a, b] * dg u = dg ![a, b] := by
      rw [mul_assoc, dg_comm ![a, b] u, inv_mul_cancel_left]
    have h3 : (GeneralLinearGroup.scalar (Fin 2) z')⁻¹ * dg ![a, b] * GeneralLinearGroup.scalar (Fin 2) z' = dg ![a, b] := by
      rw [mul_assoc, ← scalar_comm, inv_mul_cancel_left]
    rw [h1, h2, h3, hD, mul_assoc j⁻¹ (dg ![a / b / (d 0 / d 1), 1]) (dg d), conj_sc _ _ _ (scalar_comm _ j⁻¹)]
    group
  rw [hX, hE.2.2 d hd |>.1 _ _ ⟨j⁻¹ * dg ![a / b / (d 0 / d 1), 1], mul_mem (inv_mem hj) (V.dg_mem ?_), j, hj, rfl⟩,
    ← map_inv, inv_div]
  intro i
  fin_cases i
  · exact hc
  · exact one_mem _

theorem orbZ : OrbZ := by
  classical
  intro k _ _ _ _ V ω hω d hd T _ p q hpq g₀ ι hι a b hab
  letI : MulAction T (GL (Fin 2) k ⧸ V.ZJ 2) := MulAction.compHom _ ι
  have hJ : V.J 2 ≤ V.ZJ 2 := le_sup_right
  have hrel : (V.H.comap (p / q)).relIndex ((Uo k).comap (p / q)) = V.H.relIndex (Uo k) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hpq]
  have horb : ∀ y ∈ MulAction.orbit T ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2),
      ∃ u : Fin 2 → kˣ, y = ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) := by
    rintro _ ⟨s, rfl⟩
    refine ⟨![p s, q s], ?_⟩
    change ((ι s * g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _
    rw [hι]
    congr 1
    group
  have horb' : ∀ u : Fin 2 → kˣ, ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) ∈
      MulAction.orbit T ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) := by
    intro u
    obtain ⟨s, hs⟩ := hpq (u 0 / u 1)
    refine ⟨s, ?_⟩
    change ((ι s * g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _
    rw [QuotientGroup.eq, hι]
    have e : (g₀ * dg ![p s, q s] * g₀⁻¹ * g₀)⁻¹ * (g₀ * dg u) = dg (![p s, q s]⁻¹ * u) := by
      rw [dg_mul, dg_inv]
      group
    rw [e, dg_mem_ZJ V ω hω]
    have hs' : p s / q s = u 0 / u 1 := hs
    have : (![p s, q s]⁻¹ * u) 0 / (![p s, q s]⁻¹ * u) 1 = 1 := by
      simp only [Pi.mul_apply, Pi.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_div_mul_comm, ← hs']
      simp
    rw [this]
    exact one_mem _
  have main := one_orbit ((Uo k).comap (p / q)) (V.H.comap (p / q))
    (fun y : GL (Fin 2) k ⧸ V.ZJ 2 => V.fZ ω d (y.out⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * y.out))
    ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) (ω (d 1 / b) : ℂ) (a / b / (d 0 / d 1) ∈ V.H)
    (by
      intro y hy
      obtain ⟨hP, u, j, hj, e⟩ := supp_orb V ω d hd g₀ a b hab _ hy
      refine ⟨hP, ?_⟩
      have : y = ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) := by
        rw [← QuotientGroup.out_eq' y, e]
        exact QuotientGroup.mk_mul_of_mem _ (hJ hj)
      exact this ▸ horb' u)
    (by
      intro hP y hy
      obtain ⟨u, rfl⟩ := horb y hy
      have hm : (g₀ * dg u)⁻¹ * (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out ∈ V.ZJ 2 :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
      have e : (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out =
          g₀ * dg u * ((g₀ * dg u)⁻¹ * (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out) := by
        group
      show V.fZ ω d _ = _
      rw [e]
      exact value_orb V ω hω d hd g₀ a b hP u _ hm)
    (by
      intro y hy
      obtain ⟨u, rfl⟩ := horb y hy
      ext s
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, MonoidHom.div_apply]
      change ((ι s * (g₀ * dg u) : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _ ↔ _
      rw [QuotientGroup.eq, hι]
      have e : (g₀ * dg ![p s, q s] * g₀⁻¹ * (g₀ * dg u))⁻¹ * (g₀ * dg u) = dg ![p s, q s]⁻¹ := by
        rw [dg_inv]
        have : g₀ * dg ![p s, q s] * g₀⁻¹ * (g₀ * dg u) = g₀ * dg u * dg ![p s, q s] := by
          rw [mul_assoc g₀ (dg u), dg_comm u]
          group
        rw [this]
        group
      rw [e, dg_mem_ZJ V ω hω]
      have : (![p s, q s]⁻¹ : Fin 2 → kˣ) 0 / (![p s, q s]⁻¹ : Fin 2 → kˣ) 1 = (p s / q s)⁻¹ := by
        simp
        rw [div_eq_mul_inv, mul_comm]
      rw [this, inv_mem_iff])
  rw [hrel] at main
  refine ⟨main.1, ?_⟩
  unfold orb
  exact main.2

end UpperTheory.V.Z.Sym.Sig

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.TauOfRoots
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem tau_of_roots {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (a : kˣ) (τ : k)
    (h : (X - C (a : k)) * (X - C 1) * (X - C ((a⁻¹ : kˣ) : k)) = ((X - 1) * (X ^ 2 - C τ * X + 1) : k[X])) :
    τ = (a : k) + ((a⁻¹ : kˣ) : k) := by
  have hu : C (a : k) * C ((a⁻¹ : kˣ) : k) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  have e1 : (X - C (a : k)) * (X - C 1) * (X - C ((a⁻¹ : kˣ) : k)) =
      (X - 1) * (X ^ 2 - C ((a : k) + ((a⁻¹ : kˣ) : k)) * X + 1) := by
    rw [C_add, C_1]
    linear_combination (X - 1) * hu
  rw [e1] at h
  have hne : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
  have h' := mul_left_cancel₀ hne h
  have hc := congrArg (fun q : k[X] => q.coeff 1) h'
  simp only [coeff_add, coeff_sub, coeff_C_mul_X, coeff_X_pow, coeff_one] at hc
  norm_num at hc
  rw [Units.val_inv_eq_inv_val]
  linear_combination hc

private theorem charpoly_dg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b c : kˣ) :
    (((dg ![a, b, c] : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).charpoly = (X - C (a : k)) * (X - C (b : k)) * (X - C (c : k)) := by
  rw [dg.eq_1, val_diagT, charpoly_diagonal]
  simp [Fin.prod_univ_three]

theorem UpperTheory.V.Z.Sym.Sig.okG :
    UpperTheory.V.Z.Sym.Sig.OkG := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht
  simp only [Lev.data.eq_1, Set.mem_setOf_eq] at ht ⊢
  obtain ⟨hbij, htheta, -, htau⟩ := eU_facts k O hO h2 Δ s hs hs0
  have hinv : ∀ (d : Fin 3 → kˣ) (u : GL (Fin 3) k), u ∈ V.J 3 →
      ∀ u' ∈ V.J 3, ∀ g, V.unitaryDoubleCosetIndicator d (u * g * th k 3 u') = V.unitaryDoubleCosetIndicator d g :=
    fun d u hu u' hu' g => ((eqG k V 1 ∅ ∅ 1 1 d).1 u hu u' hu' g).1
  have hfin : ∀ d : Fin 3 → kˣ,
      {y : GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3) | V.unitaryDoubleCosetIndicator d (Quotient.out y) ≠ 0}.Finite :=
    fun d => (eqG k V 1 ∅ ∅ 1 1 d).2.1
  refine ⟨?_, ?_, ?_⟩
  · intro u hu y
    rw [Subgroup.mem_comap] at hu
    constructor
    · simp only [map_mul, Lev.unitaryHeckeTestSum.eq_1]
      refine Finset.sum_congr rfl fun z _ => ?_
      simpa [map_one] using hinv _ (eU hs u) hu 1 (Subgroup.one_mem _) (eU hs y)
    · simp only [map_mul, htheta, Lev.unitaryHeckeTestSum.eq_1]
      refine Finset.sum_congr rfl fun z _ => ?_
      simpa using hinv _ 1 (Subgroup.one_mem _) (eU hs u) hu (eU hs y)
  · let ψ : U3 Δ ⧸ Subgroup.comap (eU hs) (V.J 3) → GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3) :=
      fun x => QuotientGroup.mk (th k 3 (eU hs (Quotient.out x)))
    have hψ : Function.Injective ψ := by
      intro x x' hxx
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
      rw [QuotientGroup.eq] at hxx ⊢
      rw [Subgroup.mem_comap]
      obtain ⟨j, hj, hjeq⟩ := Subgroup.mem_map.1 hxx
      have hth : Function.Injective (th k 3) := fun a b hab => by
        have := congrArg (th k 3) hab
        rwa [(thFacts k V).2.2.2.1, (thFacts k V).2.2.2.1] at this
      rw [← map_inv, ← map_mul, ← map_inv, ← map_mul] at hjeq
      rw [← hth hjeq]
      exact hj
    let T : Set (GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3)) :=
      ⋃ y ∈ Ry, {z | V.unitaryDoubleCosetIndicator ![t * (unif k)⁻¹, y, (unif k)⁻¹] (Quotient.out z) ≠ 0}
    have hT : T.Finite := Set.Finite.biUnion Ry.finite_toSet fun y _ => hfin _
    refine (hT.preimage hψ.injOn).subset fun x hx => ?_
    have hx' : V.unitaryHeckeTestSum Ry t (eU hs (theta Δ (Quotient.out x))) ≠ 0 := hx
    rw [htheta, Lev.unitaryHeckeTestSum.eq_1] at hx'
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
    simp only [Set.mem_preimage, T, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨y, hy, ?_⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.map (th k 3) (V.J 3))
      (th k 3 (eU hs (Quotient.out x)))
    obtain ⟨j, hj, hjm⟩ := Subgroup.mem_map.1 m.2
    change V.unitaryDoubleCosetIndicator _ (Quotient.out (QuotientGroup.mk (th k 3 (eU hs (Quotient.out x))) :
      GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3))) ≠ 0
    rw [hm, ← hjm]
    have e := hinv ![t * (unif k)⁻¹, y, (unif k)⁻¹] 1 (Subgroup.one_mem _) j hj
      (th k 3 (eU hs (Quotient.out x)))
    rw [one_mul] at e
    rw [e]
    exact hne
  · intro δ τ hτ hne
    rw [Lev.unitaryHeckeTestSum.eq_1] at hne
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hv : (valuation k) ((unif k : kˣ) : k) < 1 := by
      rw [GlAx.unif_spec]
      exact uniformizer_lt_one
    have hv0 : 0 < (valuation k) ((unif k : kˣ) : k) := by
      rw [zero_lt_iff]
      exact (_root_.map_ne_zero _).2 (unif k).ne_zero
    obtain ⟨hy1, hy2⟩ := hRy.1 y hy
    have h01 : (valuation k) ((t * (unif k)⁻¹ : kˣ) : k) < (valuation k) (y : k) := by
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← div_eq_mul_inv,
        div_lt_iff₀ hv0]
      calc (valuation k) (t : k) < (valuation k) ((unif k : kˣ) : k) ^ 2 := ht
        _ = (valuation k) ((unif k : kˣ) : k) * (valuation k) ((unif k : kˣ) : k) := sq _
        _ ≤ (valuation k) (y : k) * (valuation k) ((unif k : kˣ) : k) := by gcongr
    have h12 : (valuation k) (y : k) < (valuation k) (((unif k)⁻¹ : kˣ) : k) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact hy2.trans_lt ((one_lt_inv₀ hv0).2 hv)
    have hSD : SDom ![t * (unif k)⁻¹, y, (unif k)⁻¹] := by
      rw [SDom.eq_1]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      all_goals first
        | exact h01
        | exact h12
        | exact h01.trans h12
    obtain ⟨g₀, x, y', z, hδ, hH⟩ := supp0 k V _ hSD _ hne
    have hd : (![t * (unif k)⁻¹, y, (unif k)⁻¹] 0 / ![t * (unif k)⁻¹, y, (unif k)⁻¹] 2 : kˣ) = t := by
      simp
    rw [hd] at hH
    have hcp := (htau δ τ).1 hτ
    rw [hδ, (normalG k).1 g₀ x y' z] at hcp
    have hc2 : ((g₀ * dg ![x / z, 1, z / x] * g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly
        = (X - C ((x / z : kˣ) : k)) * (X - C 1) * (X - C (((x / z)⁻¹ : kˣ) : k)) := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, charpoly_units_conj, charpoly_dg,
        inv_div, Units.val_one]
    rw [hc2] at hcp
    have hτ' := tau_of_roots h2 (x / z) τ hcp
    rw [Ind.eq_1]
    refine ⟨x / z / t, hH, ?_⟩
    have hm : t * (x / z / t) = x / z := by
      rw [mul_comm]
      exact div_mul_cancel (x / z) t
    rw [hm]
    exact hτ'

end
end

