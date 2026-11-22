import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.StTwTens

theorem finsum_prod_mul' {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  have hsupp : Function.support (fun z : α × β => u z.1 * v z.2) =
      Function.support u ×ˢ Function.support v := by
    ext z
    simp only [Function.mem_support, Set.mem_prod, ne_eq, mul_eq_zero, not_or]
  by_cases hu : (Function.support u).Finite
  · by_cases hv : (Function.support v).Finite
    · exact GlobalTheory.BCT.OrbProd.finsum_prod_mul_of_finite u v hu hv
    · have hv' : (Function.support v).Infinite := hv
      rw [finsum_of_infinite_support hv', mul_zero]
      rcases (Function.support u).eq_empty_or_nonempty with h | h
      · have hu0 : u = 0 := Function.support_eq_empty_iff.mp h
        simp [hu0]
      · apply finsum_of_infinite_support
        rw [hsupp]
        exact Set.Infinite.prod_right hv' h
  · have hu' : (Function.support u).Infinite := hu
    rw [finsum_of_infinite_support hu', zero_mul]
    rcases (Function.support v).eq_empty_or_nonempty with h | h
    · have hv0 : v = 0 := Function.support_eq_empty_iff.mp h
      simp [hv0]
    · apply finsum_of_infinite_support
      rw [hsupp]
      exact Set.Infinite.prod_left hu' h

section Gen

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G']

theorem twOrb_prod' (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G')
    (f : G → ℂ) (f' : G' → ℂ)
    (hf : ∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0)
    (hf' : ∀ x : G', (rStab fun k : K' => f' ((x * k)⁻¹ * δ' * θ' (x * k))).index ≠ 0) :
    twOrb (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) = twOrb θ K δ f * twOrb θ' K' δ' f' := by
  rw [GlobalTheory.BCT.OrbProd.twOrb_eq, GlobalTheory.BCT.OrbProd.twOrb_eq θ, GlobalTheory.BCT.OrbProd.twOrb_eq θ',
    GlobalTheory.BCT.OrbProd.twCent_prod θ θ' δ δ', ← finsum_prod_mul',
    ← finsum_comp_equiv (Equiv.ofBijective _ (GlobalTheory.BCT.OrbProd.dcPair_bij (twCent θ δ) K (twCent θ' δ') K'))]
  refine finsum_congr fun z => ?_
  obtain ⟨t, k, ht, hk, hq⟩ := DoubleCoset.mk_out_eq_mul ((twCent θ δ).prod (twCent θ' δ')) (K.prod K')
    (Quotient.out z.1, Quotient.out z.2)
  rw [Subgroup.mem_prod] at ht hk
  have hdc : GlobalTheory.BCT.OrbProd.dcPair (twCent θ δ) K (twCent θ' δ') K' z =
      DoubleCoset.mk ((twCent θ δ).prod (twCent θ' δ')) (K.prod K') (Quotient.out z.1, Quotient.out z.2) := rfl
  have hpt : t * (Quotient.out z.1, Quotient.out z.2) * k =
      (t.1 * Quotient.out z.1 * k.1, t.2 * Quotient.out z.2 * k.2) := rfl
  rw [Equiv.ofBijective_apply, hdc, hq, hpt,
    GlobalTheory.BCT.OrbProd.orbTerm_prod θ θ' K K' δ δ' f f' _ _ (hf _) (hf' _),
    GlobalTheory.BCT.OrbProd.orbTerm_inv θ K δ f hf ht.1 hk.1, GlobalTheory.BCT.OrbProd.orbTerm_inv θ' K' δ' f' hf' ht.2 hk.2]

end Gen

section Cl

variable {G G' : Type} [Group G] [Group G']

theorem twRel_equiv (θ : G →* G) : Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp [mul_assoc]⟩
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨g', rfl⟩
    exact ⟨g * g', by simp [mul_assoc]⟩

def mkC (θ : G →* G) (x : G) : TwCl θ := Quot.mk _ x

theorem rel_of_mkC_eq (θ : G →* G) {x y : G} (h : mkC θ x = mkC θ y) : ∃ g, y = g⁻¹ * x * θ g :=
  (twRel_equiv θ).eqvGen_iff.mp (Quot.eqvGen_exact h)

theorem mkC_eq (θ : G →* G) {x y : G} (g : G) (h : y = g⁻¹ * x * θ g) : mkC θ x = mkC θ y :=
  Quot.sound (r := fun a b : G => ∃ g, b = g⁻¹ * a * θ g) ⟨g, h⟩

theorem mkC_rep (θ : G →* G) (c : TwCl θ) : mkC θ c.rep = c := by
  exact Quot.out_eq c

def clPair (θ : G →* G) (θ' : G' →* G') (c : TwCl (θ.prodMap θ')) : TwCl θ × TwCl θ' :=
  (mkC θ c.rep.1, mkC θ' c.rep.2)

theorem clPair_bij (θ : G →* G) (θ' : G' →* G') : Function.Bijective (clPair θ θ') := by
  constructor
  · intro c d h
    have h1 : mkC θ c.rep.1 = mkC θ d.rep.1 := congrArg Prod.fst h
    have h2 : mkC θ' c.rep.2 = mkC θ' d.rep.2 := congrArg Prod.snd h
    obtain ⟨g, hg⟩ := rel_of_mkC_eq θ h1
    obtain ⟨g', hg'⟩ := rel_of_mkC_eq θ' h2
    calc c = mkC (θ.prodMap θ') c.rep := (mkC_rep _ c).symm
      _ = mkC (θ.prodMap θ') d.rep :=
        mkC_eq _ (g, g') (Prod.ext (by simpa using hg) (by simpa using hg'))
      _ = d := mkC_rep _ d
  · rintro ⟨a, b⟩
    refine ⟨mkC (θ.prodMap θ') (a.rep, b.rep), ?_⟩
    obtain ⟨g, hg⟩ := rel_of_mkC_eq (θ.prodMap θ')
      (mkC_rep (θ.prodMap θ') (mkC (θ.prodMap θ') (a.rep, b.rep)))
    have h1 : a.rep = g.1⁻¹ * (mkC (θ.prodMap θ') (a.rep, b.rep)).rep.1 * θ g.1 := by
      simpa using congrArg Prod.fst hg
    have h2 : b.rep = g.2⁻¹ * (mkC (θ.prodMap θ') (a.rep, b.rep)).rep.2 * θ' g.2 := by
      simpa using congrArg Prod.snd hg
    refine Prod.ext ?_ ?_
    · exact (mkC_eq θ g.1 h1).trans (mkC_rep θ a)
    · exact (mkC_eq θ' g.2 h2).trans (mkC_rep θ' b)

end Cl

theorem charpoly_conj {R m : Type} [CommRing R] [Fintype m] [DecidableEq m] (g X : GL m R) :
    (g⁻¹ * X * g : GL m R).val.charpoly = X.val.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g X.val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rStab_index_ne_zero {n : ℕ} {w : Pl E} {K' : Subgroup (GLw n w)} {φ : GLw n w → ℂ}
    (hK : IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K') (hφ : IsHecke K' φ) (δ x : GLw n w) :
    (rStab fun k : GlobalTheory.LFun.KGL w n => φ ((x * k)⁻¹ * δ * thL n w (x * k))).index ≠ 0 := by
  obtain ⟨hKo, -, hKθ⟩ := hK
  obtain ⟨-, hinv⟩ := hφ
  have hcpt : CompactSpace (GlobalTheory.LFun.KGL w n) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  have hopen : IsOpen ((K'.subgroupOf (GlobalTheory.LFun.KGL w n) : Subgroup (GlobalTheory.LFun.KGL w n)) :
      Set (GlobalTheory.LFun.KGL w n)) := Subgroup.subgroupOf_isOpen (GlobalTheory.LFun.KGL w n) K' hKo
  have hfin : Finite (GlobalTheory.LFun.KGL w n ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w n)) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hH : (K'.subgroupOf (GlobalTheory.LFun.KGL w n)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : K'.subgroupOf (GlobalTheory.LFun.KGL w n) ≤
      rStab fun k : GlobalTheory.LFun.KGL w n => φ ((x * k)⁻¹ * δ * thL n w (x * k)) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [GlobalTheory.TwOrbConj.mem_rStab]
    intro j
    have hk1 : (k : GLw n w)⁻¹ ∈ K' := K'.inv_mem hk
    have hk2 : thL n w (k : GLw n w) ∈ K' := hKθ _ hk
    calc φ ((x * ↑(j * k))⁻¹ * δ * thL n w (x * ↑(j * k)))
        = φ ((↑k)⁻¹ * ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j)) * thL n w ↑k) := by
          congr 1
          simp only [Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc]
      _ = φ ((↑k)⁻¹ * ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j))) := (hinv _ hk2 _).2
      _ = φ ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j)) := (hinv _ hk1 _).1
  intro h0
  apply hH
  have hd := Subgroup.index_dvd_of_le hle
  rw [h0] at hd
  exact Nat.eq_zero_of_zero_dvd hd

theorem nrmL_charpoly_twConj (n : ℕ) (w : Pl E) (g y : GLw n w) :
    (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  have hinv := GlobalTheory.BCT.TwistInvol.thL_involutive E n w g
  unfold nrmL
  unfold thL at hinv ⊢
  split_ifs at hinv ⊢ with hs
  · simp only [MonoidHom.id_apply]
    exact charpoly_conj g y
  · have key : g⁻¹ * y * thetaGL n (cj w) g * thetaGL n (cj w) (g⁻¹ * y * thetaGL n (cj w) g) =
        g⁻¹ * (y * thetaGL n (cj w) y) * g := by
      simp only [map_mul, map_inv, hinv]
      group
    rw [key]
    exact charpoly_conj g _

private theorem charpoly_nrmL_rep_eq_and_twOrb_rep_eq {n : ℕ} {w : Pl E} {K' : Subgroup (GLw n w)} {φ : GLw n w → ℂ}
    (hK : IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K') (hφ : IsHecke K' φ) (x : GLw n w) :
    (nrmL n w (mkC (thL n w) x).rep).val.charpoly = (nrmL n w x).val.charpoly ∧
      twOrb (thL n w) (GlobalTheory.LFun.KGL w n) (mkC (thL n w) x).rep φ =
        twOrb (thL n w) (GlobalTheory.LFun.KGL w n) x φ := by
  obtain ⟨g, hg⟩ := rel_of_mkC_eq (thL n w) (mkC_rep (thL n w) (mkC (thL n w) x))
  constructor
  · have h := nrmL_charpoly_twConj n w g (mkC (thL n w) x).rep
    rw [← hg] at h
    exact h.symm
  · have h := GlobalTheory.TwOrbConj.twOrb_twConj (GLw n w) (thL n w) (GlobalTheory.LFun.KGL w n) (mkC (thL n w) x).rep g φ
      (fun y => rStab_index_ne_zero hK hφ _ y)
    rw [← hg] at h
    exact h.symm

theorem stTw2_tens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (Q₁ Q₂ : (w.adicCompletion E)[X])
    (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw b w)) (φ₁ : GLw a w → ℂ) (φ₂ : GLw b w → ℂ),
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) K₁ → IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) K₂ → IsHecke K₁ φ₁ →
    IsHecke K₂ φ₂ → stTw2 a b w Q₁ Q₂ (tens φ₁ φ₂) = stTw a w Q₁ φ₁ * stTw b w Q₂ φ₂ := by
  intro E _ _ _ a b w Q₁ Q₂ K₁ K₂ φ₁ φ₂ h₁ h₂ h₃ h₄
  unfold stTw2 stTw tens clSum
  rw [← finsum_prod_mul', ← finsum_comp_equiv (Equiv.ofBijective _ (clPair_bij (thL a w) (thL b w)))]
  refine finsum_congr fun c => ?_
  have hcl : clPair (thL a w) (thL b w) c = (mkC (thL a w) c.rep.1, mkC (thL b w) c.rep.2) := rfl
  obtain ⟨hc₁, ho₁⟩ := charpoly_nrmL_rep_eq_and_twOrb_rep_eq h₁ h₃ c.rep.1
  obtain ⟨hc₂, ho₂⟩ := charpoly_nrmL_rep_eq_and_twOrb_rep_eq h₂ h₄ c.rep.2
  have ho : twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) c.rep
      (fun y => φ₁ y.1 * φ₂ y.2) =
      twOrb (thL a w) (GlobalTheory.LFun.KGL w a) c.rep.1 φ₁ * twOrb (thL b w) (GlobalTheory.LFun.KGL w b) c.rep.2 φ₂ :=
    twOrb_prod' (thL a w) (thL b w) _ _ c.rep.1 c.rep.2 φ₁ φ₂ (fun x => rStab_index_ne_zero h₁ h₃ _ x)
      (fun x => rStab_index_ne_zero h₂ h₄ _ x)
  rw [Equiv.ofBijective_apply, hcl]
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul, hc₁, hc₂, ho₁, ho₂, ho]
  by_cases hA : (nrmL a w c.rep.1).val.charpoly = Q₁ <;>
    by_cases hB : (nrmL b w c.rep.2).val.charpoly = Q₂ <;> simp [hA, hB]

end GlobalTheory.BCT.StTwTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionDensitiesPartitionUnityEqZero
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_corrDens_eq_zero : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), ∀ {ι : Type} [Fintype ι] (ρ : ι → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) → (∀ y, ∑ i, ρ i y = 1) → ∀ (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ), y ∈ c.e.source → ∑ i, corrDens E H₀ H (ρ i) c y = 0 := by
  intro F _ σ X m E O H H₀ ι _ ρ hρ h1 c y hy
  have hc : IsHoloChart c.e := c.holo
  have key := GlobalTheory.T.sum_transgressionTopCoeffComplex_partitionOfUnity_eq_zero (fun i v => ρ i (c.e.symm v))
    (fun v => H₀ (E.nonempty (under y)).choose (c.e.symm v) ())
    (fun v => H (E.nonempty (under y)).choose (c.e.symm v) ()) (c.e y)
    (fun i => (contDiffAt_holoChart hc hy (hρ i y)).differentiableAt (by simp))
    (fun x => h1 _)
  simp only [corrDens, corrTop]
  rw [← Finset.mul_sum, ← Complex.re_sum, key]
  simp

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystem
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.SymCols

variable {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K A)

theorem word_const (l : Fin N → K) (n : ℕ) : word mul (fun _ : Fin n => l) = mul l ^ n := by
  simp [word, List.ofFn_const, List.prod_replicate]

theorem join_fun {D : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K) (b : Fin (D + 1)) :
    (fun k => join s l (b, k)) = Fin.lastCases (motive := fun _ => Fin N → K) l s b := by
  induction b using Fin.lastCases with
  | last => funext k; simp [join]
  | cast i => funext k; simp [join]

theorem word_join (hc : ∀ u v, mul u * mul v = mul v * mul u) {D t : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K)
    (β : Fin t → Fin (D + 1)) (α : Fin D →₀ ℕ)
    (hα : ∀ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card = α i) :
    word mul (fun q k => join s l (β q, k)) =
      pw mul s α * mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card := by
  classical
  let P := Submonoid.closure (Set.range mul)
  letI : CommMonoid P := Submonoid.closureCommMonoidOfComm _ (by rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩; exact hc u v)
  let G : (Fin N → K) → P := fun u => ⟨mul u, Submonoid.subset_closure ⟨u, rfl⟩⟩
  let φ : P →* Module.End K A := P.subtype
  have key : ∀ {n : ℕ} (f : Fin n → P), (List.ofFn fun i => φ (f i)).prod = φ (∏ i, f i) := by
    intro n f
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  let H : Fin (D + 1) → Fin N → K := Fin.lastCases (motive := fun _ => Fin N → K) l s
  have h1 : word mul (fun q k => join s l (β q, k)) = φ (∏ q, G (H (β q))) := by
    rw [← key]
    simp only [word, join_fun]
    rfl
  have h2 : pw mul s α = φ (∏ i, G (s i) ^ α i) := by
    rw [← key]
    simp only [pw, map_pow]
    rfl
  rw [h1, h2, show mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card = φ (G l ^ (Finset.univ.filter fun q => β q = Fin.last D).card) from (map_pow φ (G l) _).symm, ← map_mul]
  congr 1
  rw [Finset.prod_comp (fun b => G (H b)) β]
  rw [Finset.prod_subset (Finset.subset_univ _)]
  · rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [H, hα]
    · simp [H]
  · intro b _ hb
    have : (Finset.univ.filter fun q => β q = b).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q _ hq
      exact hb (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩)
    rw [this, pow_zero]

theorem card_fibers {D t : ℕ} (β : Fin t → Fin (D + 1)) :
    ∑ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card +
      (Finset.univ.filter fun q => β q = Fin.last D).card = t := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := β)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  rw [Fin.sum_univ_castSucc] at this
  exact this.symm

end GlobalTheory.HSShort.SymCols

open GlobalTheory.HSShort.SymCols in
theorem GlobalTheory.HSShort.symbols_of_columns : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → ∀ l : Fin S.N → E, (∀ (a : Fin (S.T - S.D)) (α : MonoDeg (Fin S.D) a) (p : Fin δ), ∃ h : word Φ.mul (fun q k => join s l ((col (ix (⟨a, α⟩, p))).β q, k)) (Φ.ι (col (ix (⟨a, α⟩, p))).x) ∈ Φ.U a, ∀ α' p', Φ.sym a ⟨_, h⟩ (α', p') = if α'.1 = α.1 then (∑ k, l k * Φ.y p' k) ^ (S.T - a) * Φ.res (Φ.ι (m p)) p' else 0) ∧ ∀ k, k ∉ Set.range ix → (col k).j = S.D → word Φ.mul (fun q j => join s l ((col k).β q, j)) (Φ.ι (col k).x) ∈ Φ.U (S.T - S.D) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d col m ix hsh l
  refine ⟨fun a α p => ?_, fun k hk hj => ?_⟩
  · set κ := col (ix (⟨a, α⟩, p)) with hκ
    have hj : κ.j = 0 := hsh.x_j _
    have hx : (κ.x : A) = m p := hsh.x_vec _
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => κ.β q = i.castSucc).card = α.1 i := hsh.x_type _
    have ht : κ.t = S.T := by have := κ.add; omega
    have hdeg : ∑ i : Fin S.D, α.1 i = a := by rw [← Finsupp.degree_eq_sum]; exact α.2
    have hlast : (Finset.univ.filter fun q => κ.β q = Fin.last S.D).card = S.T - a := by
      have := card_fibers κ.β
      simp only [htype, hdeg] at this
      omega
    have heq : word Φ.mul (fun q k => join s l (κ.β q, k)) (Φ.ι κ.x) =
        pw Φ.mul s α.1 (word Φ.mul (fun _ : Fin (S.T - a) => l) (Φ.ι (m p))) := by
      rw [word_join Φ.mul Φ.comm s l κ.β α.1 htype, hlast, word_const, Module.End.mul_apply, hx]
    obtain ⟨h, hsym⟩ := Φ.mono a (by omega) α (fun _ => l) (Φ.ι (m p))
      (Submodule.subset_span ⟨(m p : A), (m p).2, rfl⟩)
    rw [heq]
    refine ⟨h, fun α' p' => ?_⟩
    rw [hsym]
    simp
  · have hrest := hsh.rest k hk
    have hno : ∀ q, (col k).β q ≠ Fin.last S.D := by
      rcases hrest with h | h
      · exact h.2
      · have := hS.le_T; omega
    classical
    let α : Fin S.D →₀ ℕ := Finsupp.equivFunOnFinite.symm
      (fun i => (Finset.univ.filter fun q => (col k).β q = i.castSucc).card)
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => (col k).β q = i.castSucc).card = α i := fun i => rfl
    have h0 : (Finset.univ.filter fun q => (col k).β q = Fin.last S.D).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun q _ => hno q
    have ht : (col k).t = S.T - S.D := by have := (col k).add; omega
    have hdeg : α.degree = S.T - S.D := by
      rw [Finsupp.degree_eq_sum]
      have := card_fibers (col k).β
      rw [h0] at this
      simpa [α, ht] using this
    rw [word_join Φ.mul Φ.comm s l (col k).β α htype, h0, pow_zero, mul_one, Φ.div]
    refine Submodule.mem_iSup_of_mem ⟨α, hdeg⟩ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨((col k).x : A), ?_, rfl⟩))
    have key : ∀ (j : ℕ) (x : S.V j), j = S.D → (x : A) ∈ S.V S.D := by rintro j x rfl; exact x.2
    exact key _ _ hj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExponentialProjectionStatement
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_exponential_projection : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → ∀ x y : Fin n → ℂ, (star x ᵥ* J) ⬝ᵥ x = 0 → (star y ᵥ* J) ⬝ᵥ y = 0 → (star x ᵥ* J) ⬝ᵥ y = 1 → ∀ ζ : ℂ, IsSkew J (ζ • projL J x y - star ζ • projL J y x) ∧ NormedSpace.exp (ζ • projL J x y - star ζ • projL J y x) = torMat J x y (Complex.exp ζ) := by
  first | exact @GlobalTheory.TorFin.TorusExp.exp_torus | exact GlobalTheory.TorFin.TorusExp.exp_torus | (intros; apply GlobalTheory.TorFin.TorusExp.exp_torus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchBasicOpenMorphismUniqueStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivSqZeroExt_pinch_basicOpen_morphism_unique : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (V : (Sp (TrivSqZeroExt R M)).Opens) (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)), V = (Sp (TrivSqZeroExt R M)).basicOpen s → ∀ (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1 → ∀ g₁ g₂ : V.toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₁ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₂ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap β).resLE V _ le_rfl ≫ g₁ = (spMap β).resLE V _ le_rfl ≫ g₂ → g₁ = g₂ := by
  first | exact @GlobalTheory.PinchUniq.uniq | exact GlobalTheory.PinchUniq.uniq | (intros; apply GlobalTheory.PinchUniq.uniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchExistsExtendBasicOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivSqZeroExt_pinch_exists_extend_basicOpen : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∀ (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)) (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s ≤ x ⁻¹ᵁ U.1 → ∃ g : ((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ x ∧ (spMap β).resLE _ _ le_rfl ≫ g = (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ z := by
  first | exact @GlobalTheory.Pinch.exists_extend_basicOpen | exact GlobalTheory.Pinch.exists_extend_basicOpen | (intros; apply GlobalTheory.Pinch.exists_extend_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistInvTransposeDetCharStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_inv_transpose_det_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ), Nonempty (Representation.Equiv ((twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n)) (twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))))) := by
  first | exact @GlobalTheory.InvTransposeTwist.main | exact GlobalTheory.InvTransposeTwist.main | (intros; apply GlobalTheory.InvTransposeTwist.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerEquivNormOneTorusNonsplitStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizer_equiv_normOneTorus_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit β → B.σ β = β * ((-1) ^ (m - 1) * u) → Algebra.adjoin K.E {u} = ⊤ → IsUnit (GlobalTheory.TwLat.gram e b β) → ∃ φ : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β) ≃* B.T, (∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), (t : GLw m w).val = GlobalTheory.TwLat.mulMat e b (((φ t : B.T) : B.Aˣ) : B.A)) ∧ ∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), ((t : GLw m w) ∈ cptPart (twCent (thL m w) (GlobalTheory.TwLat.dlt e b β)) ↔ ((φ t : B.T) : B.Aˣ) ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  first | exact @GlobalTheory.TwLat.twCent_equiv_torus | exact GlobalTheory.TwLat.twCent_equiv_torus | (intros; apply GlobalTheory.TwLat.twCent_equiv_torus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspliStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → ∀ (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P = Q.map e.symm.toRingHom → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (a - 1) * B.g) → ∃ F : B.Cl ≃ {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q}, ∀ k : B.Cl, ∃ b : Module.Basis (Fin a) K.E B.A, ∀ i j, (((F k).1.rep.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm ((β₀ : B.A) * k.rep) (b i) (b j)) := by
  first | exact @GlobalTheory.TwClassForms.twCl_equiv_cl | exact GlobalTheory.TwClassForms.twCl_equiv_cl | (intros; apply GlobalTheory.TwClassForms.twCl_equiv_cl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLeviProj
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory.WhitHered

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def unipLevi {c : ℕ} (m : Fin c → ℕ) : Subgroup (Levi k fun a => Fin (m a)) :=
  Subgroup.pi Set.univ fun a => unipB k (Fin (m a))

variable {k}

def unipLeviProj {c : ℕ} (m : Fin c → ℕ) (a : Fin c) : unipLevi k m →* unipB k (Fin (m a)) :=
  ((Pi.evalMonoidHom (fun b => GL (Fin (m b)) k) a).comp (unipLevi k m).subtype).codRestrict _
    fun u => u.2 a (Set.mem_univ a)

def whitLevi (ψ : AddChar k Circle) {c : ℕ} (m : Fin c → ℕ) : unipLevi k m →* ℂˣ :=
  ∏ a, (GlobalTheory.LocGL.whitChar ψ (m a)).comp (unipLeviProj m a)

variable {N c : ℕ} {m : Fin c → ℕ}

def blockColRank (e : (Σ a, Fin (m a)) ≃ Fin N) (g : GL (Fin N) k) (a : Fin c) (j : Fin N) : ℕ :=
  ((g : Matrix (Fin N) (Fin N) k).submatrix (fun i : {i : Fin N // a ≤ blk e i} => i.1)
    (fun j' : {j' : Fin N // j' ≤ j} => j'.1)).rank

def cellHt (e : (Σ a, Fin (m a)) ≃ Fin N) (g : GL (Fin N) k) : ℕ :=
  ∑ a, ∑ j, blockColRank e g a j

def cellHtMax (e : (Σ a, Fin (m a)) ≃ Fin N) : ℕ :=
  ∑ a : Fin c, ∑ j : Fin N, min (Fintype.card {i : Fin N // a ≤ blk e i}) ((j : ℕ) + 1)

end GlobalTheory.WhitHered

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEntireFactorIsThetaFunctionStandardStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_vacuum_entire_factor_isThetaFunction_standard : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (colLat frS : Set _) (colLat frT : Set _) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) := by
  first | exact @GlobalTheory.ThetaLawOF.theta_of_vacuum_real | exact GlobalTheory.ThetaLawOF.theta_of_vacuum_real | (intros; apply GlobalTheory.ThetaLawOF.theta_of_vacuum_real <;> assumption)
end

