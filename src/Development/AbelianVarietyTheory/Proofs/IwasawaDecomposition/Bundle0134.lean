import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0131
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivAt0CompMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx
open scoped ContDiff

namespace GlobalTheory.Mem.JetChain

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem eq_sum_coordX (z : VCx ι a b) : z = ∑ k : DVar ι a b, z k.1 k.2.1 k.2.2 • coordX k := by
  classical
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (τ, i, j)]
  · simp [coordX]
  · rintro ⟨τ', i', j'⟩ _ h
    have : ¬ (τ = τ' ∧ i = i' ∧ j = j') := by
      rintro ⟨rfl, rfl, rfl⟩
      exact h rfl
    simp [coordX, this]
  · simp

theorem exists_derivAt0 (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) {n : ℕ} (f : Fin n → DVar ι a b) :
    ∃ e : DVar ι a b →₀ ℕ, e.degree = n ∧ iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) = derivAt0 G e := by
  classical
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  set e : DVar ι a b →₀ ℕ := Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b)) with he
  have hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b)) := by
    rw [he, Multiset.toFinsupp_toMultiset]
  have hc : (Finsupp.toMultiset e).card = n := by rw [hm]; simp
  refine ⟨e, ?_, ?_⟩
  · rw [← hc, Finsupp.card_toMultiset]; rfl
  have p : ((List.ofFn f).map coordX).Perm ((Finsupp.toMultiset e).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hm]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p n (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx ι a b) (w : Fin n' → VCx ι a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  unfold derivAt0
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp
  · simp

theorem derivAt0_comp_mem : ∀ (ι : Type) [Fintype ι] (a b n : ℕ) (K₀ : Subfield ℂ) (G : VCx ι a b → ℂ) (L : VCx ι a b →ₗ[ℂ] VCx ι a b) (κ : ℂ), (∀ k : ℕ, ContDiff ℂ k G) → (∀ k τ i j, L (coordX k) τ i j ∈ K₀) → (∀ e : DVar ι a b →₀ ℕ, e.degree = n → κ * derivAt0 G e ∈ K₀) → ∀ e : DVar ι a b →₀ ℕ, e.degree = n → κ * derivAt0 (fun z => G (L z)) e ∈ K₀ := by
  intro ι _ a b n K₀ G L κ hG hL hK e he
  classical
  have hc : (Finsupp.toMultiset e).card = n := by
    rw [← he, Finsupp.card_toMultiset]; rfl
  subst hc
  let T : VCx ι a b →L[ℂ] VCx ι a b := LinearMap.toContinuousLinearMap L
  have h1 : (fun z => G (L z)) = G ∘ T := rfl
  have key : ∀ g : Fin (Finsupp.toMultiset e).card → DVar ι a b,
      κ * iteratedFDeriv ℂ _ G 0 (fun i => L (coordX (g i))) ∈ K₀ := by
    intro g
    have h2 : (fun i => L (coordX (g i))) =
        fun i => ∑ k : DVar ι a b, L (coordX (g i)) k.1 k.2.1 k.2.2 • coordX k :=
      funext fun i => eq_sum_coordX _
    rw [h2, ContinuousMultilinearMap.map_sum, Finset.mul_sum]
    refine sum_mem fun f _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_left_comm]
    refine mul_mem (prod_mem fun i _ => hL _ _ _ _) ?_
    obtain ⟨e', he', h⟩ := exists_derivAt0 G hG f
    rw [h]
    exact hK e' he'
  unfold derivAt0
  rw [h1, T.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact key _

end GlobalTheory.Mem.JetChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondActionOnHermitianChartClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.DiaCl

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem cl_smul_eq (b : S.β) (g : S.G b) (d : S.D b) : S.cl b (g • d) = S.cl b d :=
  congrArg (Sigma.mk b) (Quotient.sound (show (MulAction.orbitRel (S.G b) (S.D b)).r (g • d) d from ⟨g, rfl⟩))

theorem cl_rep_eq (c : S.Cl) : S.cl c.1 (S.rep c) = c := by
  obtain ⟨b, q⟩ := c
  exact congrArg (Sigma.mk b) (S.rp_spec b q)

theorem exists_move (b : S.β) (d : S.D b) : ∃ g : S.G b, g • S.rep (S.cl b d) = d :=
  (MulAction.orbitRel (S.G b) (S.D b)).symm (Quotient.exact (S.rp_spec b (Quotient.mk _ d)))

theorem dia_inj (h : A.Ok T) (b : S.β) (P : ST) (a : (Res P.1)ˣ) : Function.Injective (A.dia b P a) := by
  intro d d' hd
  have := congrArg (A.dia b P a⁻¹) hd
  rwa [← h.dia_mul, ← h.dia_mul, inv_mul_cancel, h.dia_one, h.dia_one] at this

theorem stab_dia (h : A.Ok T) (b : S.β) (P : ST) (a : (Res P.1)ˣ) (d : S.D b) :
    MulAction.stabilizer (S.G b) (A.dia b P a d) = MulAction.stabilizer (S.G b) d := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← h.dia_act]
  exact (dia_inj h b P a).eq_iff

theorem card_stab_cl (b : S.β) (d : S.D b) :
    Nat.card (S.Stab (S.cl b d)) = Nat.card (MulAction.stabilizer (S.G b) d) := by
  obtain ⟨g, hg⟩ := exists_move (S := S) b d
  exact Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv

end GlobalTheory.Mem.Col2.DiaCl

namespace GlobalTheory.Mem.Col2

open DiaCl

theorem diamond_action_on_classes : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T →
    (∀ P c, S.cl c.1 (A.diaPt P 1 c) = c) ∧
    (∀ P a b c, S.cl c.1 (A.diaPt P (a * b) c) = S.cl c.1 (A.diaPt P a (S.cl c.1 (A.diaPt P b c)))) ∧
    ∀ P a c, Nat.card (S.Stab (S.cl c.1 (A.diaPt P a c))) = Nat.card (S.Stab c) := by
  intro E K _ _ _ _ n S ST A T _ h
  refine ⟨fun P c => ?_, fun P a b c => ?_, fun P a c => ?_⟩
  · unfold TDat.diaPt
    rw [h.dia_one, cl_rep_eq]
  · unfold TDat.diaPt
    obtain ⟨g, hg⟩ := exists_move (S := S) c.1 (A.dia c.1 P b (S.rep c))
    rw [← cl_smul_eq c.1 g (A.dia c.1 P a _), ← h.dia_act, hg, h.dia_mul]
  · rw [card_stab_cl]
    unfold TDat.diaPt
    rw [stab_dia h]

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcretePeriodDatumPadicFiniteExtension
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.PdEx

variable {l : ℕ} [Fact l.Prime]

def actOf {G k B : Type} [Group G] [CommRing k] [CommRing B] [Algebra k B] (s : G → B →+* B)
    (hmul : ∀ g h x, s (g * h) x = s g (s h x)) (hone : ∀ x, s 1 x = x)
    (hk : ∀ g c, s g (algebraMap k B c) = algebraMap k B c) : G →* (B ≃ₐ[k] B) where
  toFun g :=
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun x => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun x => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := map_mul (s g)
      map_add' := map_add (s g)
      commutes' := hk g }
  map_one' := AlgEquiv.ext fun x => hone x
  map_mul' g h := AlgEquiv.ext fun x => hmul g h x

def inc (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)

theorem inc_coe (K : FinExt l) (x : ↥(K0 K)) : ((inc K x : ↥(MaximalUnramifiedExtension l)) : Om l) = (x : Om l) := rfl

def sigK (K : FinExt l) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (h : ∀ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K) :=
  (((MaximalUnramifiedExtension l).val.comp σ).comp (inc K)).codRestrict (K0 K).toSubalgebra fun x =>
    ⟨h (inc K x) x.2.1, (σ (inc K x)).2⟩

theorem inc_sigK (K : FinExt l) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (h) (x : ↥(K0 K)) :
    inc K (sigK K σ h x) = σ (inc K x) := Subtype.ext rfl

theorem finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))

theorem fix (K : FinExt l) (g : ↥(GK K)) (x : Om l) (hx : x ∈ K.1) : (g : GQ l) x = x :=
  (IntermediateField.mem_fixingSubgroup_iff K.1 (g : GQ l)).1 g.2 x hx

theorem exists_abstract (R : LocRings l) (K : FinExt l)
    (sB : GQ l → R.B →+* R.B) (sD : GQ l → R.BdR →+* R.BdR) (φ : R.B →+* R.B) (ι : R.B →+* R.BdR)
    (F : ℤ → AddSubgroup R.BdR) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (χ : GQ l →* ℤ_[l]ˣ) (t : R.B)
    (hσ : ∀ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1)
    (sB_mul : ∀ g h x, sB (g * h) x = sB g (sB h x)) (sB_one : ∀ x, sB 1 x = x)
    (sD_mul : ∀ g h x, sD (g * h) x = sD g (sD h x)) (sD_one : ∀ x, sD 1 x = x)
    (sB_u : ∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) →
      sB g (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B c')
    (sD_o : ∀ (g : GQ l) (x : Om l), sD g (algebraMap (Om l) R.BdR x) = algebraMap (Om l) R.BdR (g x))
    (invB : ∀ b, (∀ g ∈ GK K, sB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ algebraMap ↥(MaximalUnramifiedExtension l) R.B c = b)
    (invD : ∀ b, (∀ g ∈ GK K, sD g b = b) → ∃ y ∈ K.1, algebraMap (Om l) R.BdR y = b)
    (φ_inj : Function.Injective φ)
    (φ_u : ∀ c, φ (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B (σ c))
    (φ_comm : ∀ g b, φ (sB g b) = sB g (φ b))
    (ι_u : ∀ c : ↥(MaximalUnramifiedExtension l), ι (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap (Om l) R.BdR (c : Om l))
    (ι_inj : Function.Injective ι) (ι_comm : ∀ g b, ι (sB g b) = sD g (ι b))
    (F_o : ∀ x : Om l, algebraMap (Om l) R.BdR x ∈ F 0)
    (F_anti : ∀ a, F (a + 1) ≤ F a)
    (F_mul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (F_exh : ∀ x, ∃ a, x ∈ F a) (F_sep : ∀ x, (∀ a, x ∈ F a) → x = 0)
    (F_G : ∀ g a x, x ∈ F a → sD g x ∈ F a)
    (t_unit : IsUnit t)
    (t_act : ∀ g, sB g t = algebraMap ℚ_[l] R.B ((χ g : ℤ_[l]) : ℚ_[l]) * t)
    (t_φ : φ t = (l : R.B) * t) (t1 : ι t ∈ F 1) (t2 : ι t ∉ F 2)
    (fund : ∀ b, φ b = b → ι b ∈ F 0 → ∃ c : ℚ_[l], algebraMap ℚ_[l] R.B c = b) :
    ∃ PD : WeaklyAdmissibleFiltrations.PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 R.B R.BdR,
      PD.p = l ∧ (∀ g b, PD.actB g b = sB g b) ∧ (∀ g b, PD.actdR g b = sD g b) ∧ (∀ b, PD.φ b = φ b) ∧
      (∀ b, PD.ι b = ι b) ∧ PD.t = t ∧ (∀ g, ((PD.χ g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ (g : GQ l) : ℤ_[l]) : ℚ_[l])) ∧
      (∀ a x, x ∈ PD.Fil a ↔ x ∈ F a) ∧
      ∀ (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) = (x : Om l) →
        ((PD.σ x : ↥(K0 K)) : Om l) = ((σ c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have aB : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) R.B c = algebraMap ↥(MaximalUnramifiedExtension l) R.B (inc K c) := fun _ => rfl
  have aD : ∀ c : ↥K.1, algebraMap ↥K.1 R.BdR c = algebraMap (Om l) R.BdR (c : Om l) := fun _ => rfl
  have aD0 : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) R.BdR c = algebraMap (Om l) R.BdR (c : Om l) := fun _ => rfl
  have aQ : ∀ c : ℚ_[l], algebraMap ℚ_[l] R.B c = algebraMap ↥(MaximalUnramifiedExtension l) R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) :=
    fun c => IsScalarTower.algebraMap_apply _ _ _ c
  haveI := finiteDimensional_maxUnramifiedSubfield K
  refine ⟨{
    p := l
    hp := Fact.out
    finK₀ := finiteDimensional_maxUnramifiedSubfield K
    finK := K.2
    σ := sigK K σ hσ
    σ_bij := AlgHom.bijective _
    actB := actOf (fun g : ↥(GK K) => sB g) (fun g h x => sB_mul g h x) (fun x => sB_one x)
      (fun g c => by rw [aB]; exact sB_u g _ _ (fix K g _ c.2.1))
    invB := fun b hb => by
      obtain ⟨c, hc, e⟩ := invB b fun g hg => hb ⟨g, hg⟩
      exact ⟨⟨c, hc, c.2⟩, e⟩
    φ := AlgHom.mk φ fun c => by
      change φ _ = _
      rw [aQ, φ_u, AlgHom.commutes]
    φ_inj := φ_inj
    φ_K₀ := fun c => by
      change φ _ = _
      rw [aB, aB, φ_u, inc_sigK]
    φ_comm := fun g b => φ_comm g b
    actdR := actOf (fun g : ↥(GK K) => sD g) (fun g h x => sD_mul g h x) (fun x => sD_one x)
      (fun g c => by rw [aD, sD_o, fix K g _ c.2])
    invdR := fun b hb => by
      obtain ⟨c, hc, e⟩ := invD b fun g hg => hb ⟨g, hg⟩
      exact ⟨⟨c, hc⟩, e⟩
    ι := AlgHom.mk ι fun c => by
      change ι _ = _
      rw [aB, aD0, ι_u, inc_coe]
    ι_inj := ι_inj
    ι_comm := fun g b => ι_comm g b
    Fil := fun a =>
      { carrier := F a
        add_mem' := fun hx hy => (F a).add_mem hx hy
        zero_mem' := (F a).zero_mem
        smul_mem' := fun c x hx => by
          have := F_mul 0 a _ _ (F_o (c : Om l)) hx
          rw [zero_add, ← aD, ← Algebra.smul_def] at this
          exact this }
    Fil_anti := fun a x hx => F_anti a hx
    one_mem := by
      have := F_o 1
      rw [map_one] at this
      exact this
    Fil_mul := F_mul
    Fil_exh := F_exh
    Fil_sep := F_sep
    Fil_G := fun g a x hx => F_G g a x hx
    χ := ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp χ).comp (GK K).subtype
    t := t
    t_unit := t_unit
    t_act := fun g => by
      rw [Algebra.smul_def]
      exact t_act g
    t_φ := by
      rw [Algebra.smul_def, map_natCast]
      exact t_φ
    mem_filtration_one := t1
    not_mem_filtration_two := t2
    fund := fund }, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl,
    fun _ _ => Iff.rfl, fun x c h => ?_⟩
  have : inc K x = c := Subtype.ext h.symm
  rw [← this]
  rfl

theorem exists_realPD : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l), ∃ PD, IsRealPD C K PD := by
  intro l _ C K
  obtain ⟨a1, a2, a3, a4, a5, -, -, -, -, a10, -, a12, a13⟩ := ActLaws.act_laws l
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := GlobalTheory.T.bdR_filtration_laws l
  obtain ⟨u1, u2, -, u4, u5, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  have hσ := (frob_laws l C.σ C.σ_root).2.1 K
  have so := (GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec).2.2
  have sD_o : ∀ (g : GQ l) (x : Om l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) (C.o x)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o (g x)) := fun g x => by rw [a10, so]
  have F_o : ∀ x : Om l, algebraMap (Per.BdRp l) (Per.BdR l) (C.o x) ∈ Per.FilD l 0 := fun x => by
    have h1 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := (f7 0 1).1 (by rw [map_one]; exact f2)
    have h2 : C.o x * 1 ∈ Per.FilP l 0 := Ideal.mul_mem_left _ _ h1
    rw [mul_one] at h2
    exact (f7 0 _).2 h2
  have u_z : ∀ z : ℤ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) =
      algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z)) := fun z => by
    apply u4
    have e1 : ((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l]) : ↥(MaximalUnramifiedExtension l)) : Om l) = algebraMap ℚ_[l] (Om l) (z : ℚ_[l]) :=
      (IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) (Om l) (z : ℚ_[l])).symm
    rw [C.ι_u, C.ι_j, ULaws.alg_acris, C.j_cris.on0, e1, C.o_sec.z, Subalgebra.coe_algebraMap, aDp,
      RingHom.comp_apply]
  have t_act : ∀ g : GQ l, Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) C.t) =
      C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((C.χ g : ℤ_[l]) : ℚ_[l])) * algebraMap (Per.Acris l) (Per.Bcris l) C.t :=
    fun g => by
      rw [a12, GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C g, map_mul, u_z]
  have t_φ : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t) =
      (l : Per.Bcris l) * algebraMap (Per.Acris l) (Per.Bcris l) C.t := by
    rw [a13, GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C, map_mul, map_natCast]
  have s1 : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∈ Per.FilD l 1 := by
    rw [C.ι_j]
    exact (f7 1 _).2 t2
  have s2 : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∉ Per.FilD l 2 := by
    rw [C.ι_j]
    exact fun h => t3 ((f7 2 _).1 h)
  obtain ⟨PD, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_abstract (ringsOf C) K
    (fun g => Per.σB g) (fun g => Per.σD g) (Per.φB l) C.ι (fun a => (Per.FilD l a).toAddSubgroup) C.σ C.χ
    (algebraMap (Per.Acris l) (Per.Bcris l) C.t) hσ a1 a2 a3 a4 u2 sD_o
    (InvCris.invariants_Bcris l C K) (GlobalTheory.T.bdR_galois_invariants_eq_finExt l C K) (GlobalTheory.T.frobenius_period_ring_injective l) u1 (fun g b => a5 g b) C.ι_u u4 u5
    F_o f1 f3 f4 f5 f6 t1 t_act t_φ s1 s2 (GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp l C)
  exact ⟨PD, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end GlobalTheory.MemLoc.PdEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFockFunctionalOnNablaXProducts
section
open MvPolynomial

noncomputable section
namespace GlobalTheory.FockMinorFunctional
open Formalism.L2.DIV

theorem map_int_eq_map_rat {σ K : Type} [Field K] [CharZero K] (f : MvPolynomial σ ℤ) :
    map (Int.castRingHom K) f = map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f) := by
  have e : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := RingHom.ext_int _ _
  rw [map_map, e]

theorem nablaX_eq {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (J : ∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :
    WeylLatticeDuality.nablaX N nu J = Formalism.BasicNotions.KM.nablaX N nu J := by
  unfold WeylLatticeDuality.nablaX Formalism.BasicNotions.KM.nablaX
  rfl

theorem colProd_map {K : Type} [Field K] [CharZero K] (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N)
    (J : ∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) :
    GlobalTheory.WeylMinorDual.colProd K N Y hY J =
      map (algebraMap ℚ K) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) := by
  rw [← map_int_eq_map_rat]
  unfold GlobalTheory.WeylMinorDual.colProd
  rw [fk_map_bidet]

theorem aeval_map_nablaX {K Lt : Type} [Field K] [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : ∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :
    aeval (R := K) (fun v : Lt × ℕ × Fin N =>
        if h : v.2.1 < N then (X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin N)) : Pol K Lt N) else 0)
      (map (Int.castRingHom K) (WeylLatticeDuality.nablaX N nu J)) =
      ten fun s => GlobalTheory.WeylMinorDual.colProd K N (nu s) (hY s) (J s) := by
  rw [← algebraMap_int_eq, aeval_map_algebraMap, nablaX_eq]
  exact GlobalTheory.WeylMinorDual.aeval_nablaX N nu hY J

theorem fock_functional_nablaX : ∀ (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (g : Lt → MvPolynomial (Fin N × Fin N) ℤ),
    ∃ Ψ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        Ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
          ∏ s, ((Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) (g s))
            (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) : ℚ) : ℂ_[p]) := by
  intro p _ Lt _ _ N nu hY g
  let ρ : Lt × ℕ × Fin N → Pol ℂ_[p] Lt N := fun v =>
    if h : v.2.1 < N then X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin N)) else 0
  let G : Pol ℂ_[p] Lt N := ten fun s => map (Int.castRingHom ℂ_[p]) (g s)
  refine ⟨(fockBL G).comp (aeval ρ).toLinearMap, fun J => ?_⟩
  have h1 : aeval ρ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
      ten fun s => GlobalTheory.WeylMinorDual.colProd ℂ_[p] N (nu s) (hY s) (J s) := by
    exact aeval_map_nablaX N nu hY J
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h1, fockBL_apply, GlobalTheory.WeylMinorDual.fockB_ten]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_int_eq_map_rat, colProd_map, GlobalTheory.WeylMinorDual.fockB_map]
end GlobalTheory.FockMinorFunctional
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulMemSpan
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.LevLaws

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in

theorem exists_mul_mem_span (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal)
    (hq2 : q ∉ P.asIdeal ^ 2) : ∃ s ∉ P.asIdeal, ∀ r ∈ P.asIdeal, ∃ t, s * r = q * t := by
  have h1 : P.asIdeal ∣ Ideal.span {q} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  obtain ⟨J, hJ⟩ := h1
  have h2 : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq2
    have : q ∈ P.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self q
    rw [sq]
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 h2
  refine ⟨s, hsP, fun r hr => ?_⟩
  have : r * s ∈ Ideal.span {q} := hJ ▸ Ideal.mul_mem_mul hr hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨t, by rw [mul_comm s r, ← ht, mul_comm]⟩

theorem ufGL_mulVec (γ : UF E n) (x : Sp E n) :
    Matrix.mulVec ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) x = γ.1 x :=
  LinearMap.toMatrix'_mulVec (γ.1 : Sp E n →ₗ[E] Sp E n) x

end Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem mv_dia {y : Ys X n} (p : PtY ST SG Q y) (c : DiaG X.E ST) :
    p.mv (DecoSet.dia c p.1.1.deco) =
      ⟨(⟨(DecoSet.dia c p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ := dif_pos ⟨p.1.1.2, p.2⟩

end GlobalTheory.Mem.Col2.LevLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramifiedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisInvariants_Bcris_eq_maxUnramified : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.Bcris l), (∀ g ∈ GK K, Per.σB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ C.u c = b := by
  first | exact @GlobalTheory.MemLoc.InvCris.invariants_Bcris | exact GlobalTheory.MemLoc.InvCris.invariants_Bcris | (intros; apply GlobalTheory.MemLoc.InvCris.invariants_Bcris <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityTypeStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_exponent_of_infinityType : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E), (∀ n : (E →+* ℂ) → ℤ, χ.IsAlg n → ∀ τ, expo χ τ = n τ) ∧ (∀ s : ℝ, χ.IsAbsPow s → ∀ τ, expo χ τ = s) ∧ ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ), Function.Injective (fun i => InfinitePlace.mk (φ i)) → χ.HasInf φ n → ∀ i, expo χ (φ i) = (n i : ℂ) / 2 ∧ expo χ (ComplexEmbedding.conjugate (φ i)) = -(n i : ℂ) / 2 := by
  first | exact @GlobalTheory.CuspRep.InfType.expo_of_infType | exact GlobalTheory.CuspRep.InfType.expo_of_infType | (intros; apply GlobalTheory.CuspRep.InfType.expo_of_infType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertPathCardCommLatticePathsStatement
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPath_card_comm_latticePaths : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}, (∀ R : ST, R.1 ≠ P) → (∀ w : SG, w.1 ≠ P) →
  ∀ (s t : List ℕ) (d f : DecoSet E n ST SG),
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t d.1.N Y ∧ IsInertNbr P.asIdeal s Y f.1.N}) →
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      ((d.inertNb P.asIdeal t).filter fun e => f ∈ e.inertNb P.asIdeal s).card := by
  first | exact @GlobalTheory.inertPath_card_comm | exact GlobalTheory.inertPath_card_comm | (intros; apply GlobalTheory.inertPath_card_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLawsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeLatticeDeterminantClass_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; (∀ L : SDLat H.E N, relDetT H N L.1 L.1 = 1) ∧ (∀ L L' L'' : SDLat H.E N, relDetT H N L.1 L'.1 * relDetT H N L'.1 L''.1 = relDetT H N L.1 L''.1) ∧ ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDetT H N L.1 L'.1 = QuotientGroup.mk (e1T H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  first | exact @GlobalTheory.Mem.Chr.relDetT_laws | exact GlobalTheory.Mem.Chr.relDetT_laws | (intros; apply GlobalTheory.Mem.Chr.relDetT_laws <;> assumption)
end

