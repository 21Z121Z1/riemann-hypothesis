import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountFib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.BCT.OrbLev
open Formalism.MainNotions.Gaps.CC.Fib MulAction Function

variable {G : Type} [Group G]

theorem twCent_left (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (y : G) :
    (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * δ * θ y := by
  have h : t * δ = δ * θ t := ht
  have h2 : t⁻¹ * δ * θ t = δ := by rw [mul_assoc, ← h]; group
  calc (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * (t⁻¹ * δ * θ t) * θ y := by rw [map_mul]; group
    _ = y⁻¹ * δ * θ y := by rw [h2]

theorem Gam_mul (Γ U : Subgroup G) {γ z u : G} (hγ : γ ∈ Γ) (hu : u ∈ U) :
    Gam Γ U (γ * z * u) = (Gam Γ U z).map (MulAut.conj γ).toMonoidHom := by
  ext w
  simp only [Subgroup.mem_map, mem_Gam, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨γ⁻¹ * w * γ, ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) h1) hγ, ?_⟩, by group⟩
    have := U.mul_mem (U.mul_mem hu h2) (U.inv_mem hu)
    convert this using 1; group
  · rintro ⟨v, ⟨h1, h2⟩, rfl⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem hγ h1) (Γ.inv_mem hγ), ?_⟩
    have := U.mul_mem (U.mul_mem (U.inv_mem hu) h2) hu
    convert this using 1; group

theorem Gam_eq_stab {Γ K U : Subgroup G} (hUK : U ≤ K) (x : G) (k : K) :
    Gam Γ U (x * k) = (stabilizer (Gam Γ K x) (k : K ⧸ U.subgroupOf K)).map (Gam Γ K x).subtype := by
  ext w
  constructor
  · intro hw
    let s := (stabEquiv hUK x k).symm ⟨w, hw⟩
    exact ⟨s.1, s.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    have := (stabEquiv hUK x k ⟨a, ha⟩).2
    simpa using this

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem conj_mem_cpt (T : Subgroup G) {γ : G} (hγ : γ ∈ T) {t : G}
    (ht : t ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))}) :
    (MulAut.conj γ).toMonoidHom t ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := by
  obtain ⟨h1, h2⟩ := ht
  let h : G ≃ₜ G := (Homeomorph.mulRight γ⁻¹).trans (Homeomorph.mulLeft γ)
  have hf : ⇑h = ⇑(MulAut.conj γ).toMonoidHom := by
    funext z; simp [h, MulAut.conj_apply, mul_assoc]
  refine ⟨by simpa [MulAut.conj_apply] using T.mul_mem (T.mul_mem hγ h1) (T.inv_mem hγ), ?_⟩
  rw [← MonoidHom.map_zpowers, Subgroup.coe_map, ← hf, ← h.image_closure]
  exact h2.image h.continuous

theorem cptPart_map_conj (T : Subgroup G) {γ : G} (hγ : γ ∈ T) :
    (cptPart T).map (MulAut.conj γ).toMonoidHom = cptPart T := by
  apply le_antisymm
  · rw [cptPart, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨t, ht, rfl⟩
    exact conj_mem_cpt T hγ ht
  · rw [cptPart, Subgroup.closure_le]
    intro t ht
    refine ⟨(MulAut.conj γ⁻¹).toMonoidHom t, Subgroup.subset_closure (conj_mem_cpt T (T.inv_mem hγ) ht), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem finsum_sigma_of_finite {ι : Type} {β : ι → Type} [∀ i, Finite (β i)] (h : (Σ i, β i) → ℂ)
    (hh : (support h).Finite) : ∑ᶠ p, h p = ∑ᶠ i, ∑ᶠ b, h ⟨i, b⟩ := by
  letI : ∀ i, Fintype (β i) := fun i => Fintype.ofFinite _
  set I := hh.toFinset.image Sigma.fst
  have h1 : support h ⊆ ((I.sigma fun _ => Finset.univ : Finset (Σ i, β i)) : Set _) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, and_true, I, Finset.mem_image]
    exact ⟨p, hh.mem_toFinset.2 hp, rfl⟩
  have h2 : (support fun i => ∑ᶠ b, h ⟨i, b⟩) ⊆ (I : Set ι) := by
    intro i hi
    obtain ⟨b, hb⟩ : ∃ b, h ⟨i, b⟩ ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi (finsum_eq_zero_of_forall_eq_zero hc)
    simp only [Finset.mem_coe, I, Finset.mem_image]
    exact ⟨⟨i, b⟩, hh.mem_toFinset.2 hb, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_eq_sum_of_fintype]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem finsum_orbits {H X : Type} [Group H] [MulAction H X] [Finite X] (φ : X → ℂ)
    (hφ : ∀ (h : H) y, φ (h • y) = φ y) :
    ∑ᶠ y, φ y = ∑ᶠ ω : orbitRel.Quotient H X, ((orbit H ω.out).ncard : ℂ) * φ ω.out := by
  letI : Fintype X := Fintype.ofFinite X
  haveI : Finite (orbitRel.Quotient H X) := Quotient.finite _
  letI : Fintype (orbitRel.Quotient H X) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Finset.sum_fiberwise Finset.univ (fun y => (Quotient.mk'' y : orbitRel.Quotient H X)) φ]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hmem : ∀ y, (Quotient.mk'' y : orbitRel.Quotient H X) = ω ↔ y ∈ orbit H ω.out := by
    intro y
    conv_lhs => rw [← Quotient.out_eq' ω]
    rw [Quotient.eq'']
    exact orbitRel_apply
  have hc : ∀ y ∈ Finset.univ.filter (fun y => (Quotient.mk'' y : orbitRel.Quotient H X) = ω), φ y = φ ω.out := by
    intro y hy
    obtain ⟨h, rfl⟩ := (hmem y).1 (Finset.mem_filter.1 hy).2
    exact hφ h _
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  simp [hmem]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem avg_const' {H : Type} [Group H] (u : H → ℂ) (c : ℂ) (hu : ∀ h, u h = c) : avg u = c := by
  rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H u ⊤ (fun k _ => show ∀ x, u (x * k) = u x from fun x => by rw [hu, hu]) (by simp)]
  simp only [hu, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  exact finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (QuotientGroup.subsingleton_quotient_top.elim x 1) hx)

theorem twOrb_eq_sum_smallerLevel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ k ∈ K, θ k ∈ K) → ∀ K' : Subgroup G, IsLevel θ K K' → ∀ (δ : G) (f : G → ℂ), IsHecke K' f → (∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G) | f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0}.Finite → twOrb θ K δ f = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * twOrb θ K' δ f ∧ twOrb θ K' δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G), (((twCent θ δ ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) * f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) := by
  intro G _ _ _ θ K _hKo hKc _hθK K' hL δ f hf hT hfin
  obtain ⟨hK'o, hK'K, hθK'⟩ := hL
  set T := twCent θ δ with hTdef
  set C := cptPart T with hCdef
  let F : G → ℂ := fun y => f (y⁻¹ * δ * θ y)
  have FT : ∀ t ∈ T, ∀ y, F (t * y) = F y := fun t ht y => by simp only [F, twCent_left θ δ ht y]
  have FK : ∀ y, ∀ k ∈ K', F (y * k) = F y := by
    intro y k hk
    simp only [F]
    have e : (y * k)⁻¹ * δ * θ (y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by rw [map_mul]; group
    rw [e, (hf.2 _ (hθK' k hk) _).2, (hf.2 _ (K'.inv_mem hk) _).1]
  let g : DoubleCoset.Quotient (T : Set G) (K' : Set G) → ℂ := fun q =>
    (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * F (Quotient.out q)
  have hsecond : twOrb θ K' δ f = ∑ᶠ q, g q := by
    unfold twOrb
    refine finsum_congr fun q => ?_
    congr 1
    exact avg_const' _ _ fun k => FK _ k k.2
  refine ⟨?_, hsecond⟩
  rw [hsecond]
  set S := K'.subgroupOf K with hSdef
  have hn : K'.relIndex K ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
    have ho : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := by
      rw [Subgroup.coe_subgroupOf]; exact hK'o.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite
  haveI : S.FiniteIndex := ⟨hn⟩
  haveI : Finite (K ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  have avgK : ∀ x : G, avg (fun k : K => F (x * k)) = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ y : K ⧸ S, F (x * (Quotient.out y : K)) := by
    intro x
    refine GlobalTheory.T.avg_eq_of_le_rightStabiliser K _ S (fun k hk => show ∀ z : K, F (x * ((z * k : K) : G)) = F (x * z) from fun z => ?_) hn
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact FK _ _ (Subgroup.mem_subgroupOf.1 hk)
  let e := fib (Γ := T) (K := K) hK'K
  haveI hfo : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G), Finite (orbitRel.Quotient (Gam T K (Quotient.out c)) (K ⧸ S)) :=
    fun c => Quotient.finite _
  have hc : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G),
      (((T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom).relIndex C : ℕ) : ℂ) *
        ∑ᶠ y : K ⧸ S, F (Quotient.out c * (Quotient.out y : K)) = ∑ᶠ ω, g (e.symm ⟨c, ω⟩) := by
    intro c
    have hwK : T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom = Gam T K (Quotient.out c) :=
      (Gam_eq_map T K _).symm
    rw [hwK]
    have hφ : ∀ (h : Gam T K (Quotient.out c)) (y : K ⧸ S),
        F (Quotient.out c * (Quotient.out (h • y) : K)) = F (Quotient.out c * (Quotient.out y : K)) := by
      intro h y
      have e1 : ((Quotient.out (h • y) : K) : K ⧸ S) =
          ((toK T K (Quotient.out c) h * Quotient.out y : K) : K ⧸ S) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rfl
      have hu := mk_eq_iff.1 e1.symm
      have e2 : Quotient.out c * ((Quotient.out (h • y) : K) : G) = (h : G) * (Quotient.out c * (Quotient.out y : K)) *
          (((toK T K (Quotient.out c) h * Quotient.out y : K) : G)⁻¹ * (Quotient.out (h • y) : K)) := by
        rw [Subgroup.coe_mul, toK_coe]; group
      rw [e2, FK _ _ hu, FT _ (mem_Gam.1 h.2).1]
    rw [finsum_orbits (fun y : K ⧸ S => F (Quotient.out c * (Quotient.out y : K))) hφ, mul_finsum]
    refine finsum_congr fun ω => ?_
    have hq : e.symm ⟨c, ω⟩ = DoubleCoset.mk T K' (Quotient.out c * (Quotient.out ω.out : K)) := by
      have : ω = Quotient.mk'' ((Quotient.out ω.out : K) : K ⧸ S) := by
        rw [QuotientGroup.out_eq', Quotient.out_eq']
      have h := fibRep_symm_mk hK'K Quotient.out (DoubleCoset.out_eq' T K) c (Quotient.out ω.out)
      rw [← this] at h
      exact h
    obtain ⟨γ, hγ, u, hu, hout⟩ := (DoubleCoset.eq T K' (Quotient.out c * (Quotient.out ω.out : K))
      (Quotient.out (e.symm ⟨c, ω⟩))).1 (by rw [DoubleCoset.out_eq', hq])
    have hF : F (Quotient.out (e.symm ⟨c, ω⟩)) = F (Quotient.out c * (Quotient.out ω.out : K)) := by
      rw [hout, FK _ _ hu, FT _ hγ]
    have hCc : C.map (MulAut.conj γ).toMonoidHom = C := cptPart_map_conj T hγ
    have h1 := Subgroup.relIndex_map_map_of_injective (Gam T K' (Quotient.out c * (Quotient.out ω.out : K))) C
      (f := (MulAut.conj γ).toMonoidHom) (MulAut.conj γ).injective
    rw [hCc] at h1
    have h2 : ((stabilizer (Gam T K (Quotient.out c)) ω.out).map (Gam T K (Quotient.out c)).subtype).subgroupOf
        (Gam T K (Quotient.out c)) = stabilizer (Gam T K (Quotient.out c)) ω.out :=
      Subgroup.comap_map_eq_self_of_injective (Gam T K (Quotient.out c)).subtype_injective _
    have hHC : Gam T K (Quotient.out c) ≤ C := by rw [← hwK]; exact (hT _).1
    have hw : (T ⊓ K'.map (MulAut.conj (Quotient.out (e.symm ⟨c, ω⟩))).toMonoidHom).relIndex C =
        (orbit (Gam T K (Quotient.out c)) ω.out).ncard * (Gam T K (Quotient.out c)).relIndex C := by
      rw [← Gam_eq_map, hout, Gam_mul T K' hγ hu, h1, Gam_eq_stab hK'K, QuotientGroup.out_eq',
        ← Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_subtype_le _) hHC, Subgroup.relIndex, h2,
        index_stabilizer]
    simp only [g]
    rw [hw, hF]
    push_cast
    ring
  have hsupp : (support fun p => g (e.symm p)).Finite := by
    refine (hfin.preimage e.symm.injective.injOn).subset ?_
    intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro h0
    exact hp (by simp only [g]; rw [show F (Quotient.out (e.symm p)) = 0 from h0, mul_zero])
  calc twOrb θ K δ f
      = ∑ᶠ c : DoubleCoset.Quotient (T : Set G) (K : Set G), ((K'.relIndex K : ℕ) : ℂ)⁻¹ *
          ((((T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom).relIndex C : ℕ) : ℂ) *
            ∑ᶠ y : K ⧸ S, F (Quotient.out c * (Quotient.out y : K))) := by
        unfold twOrb
        refine finsum_congr fun c => ?_
        rw [avgK]; ring
    _ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ c, ∑ᶠ ω, g (e.symm ⟨c, ω⟩) := by
        rw [← mul_finsum]; congr 1; exact finsum_congr hc
    _ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q, g q := by
        rw [← finsum_sigma_of_finite _ hsupp, finsum_comp_equiv e.symm]

end GlobalTheory.BCT.OrbLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviFubini

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev parB {a b n : ℕ} (h : a + b = n) (w : Pl E) : Subgroup (GLw n w) :=
  GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))

def levH {a b n : ℕ} (h : a + b = n) (w : Pl E) : parB h w →* GLw a w × GLw b w :=
  (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom.comp
    (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)))

theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blk h w m X ∈ parB h w := by
  rw [GlobalTheory.SmGL.mem_parab_two]
  intro j i
  rw [CtLevel.blk_val]
  show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
    (CtLevel.blkEq h (Sum.inr j)) (CtLevel.blkEq h (Sum.inl i)) = 0
  simp

theorem blk_mul_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m m' : GLw a w × GLw b w)
    (X X' : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m X * blk h w m' X' = blk h w (m * m') (X' + (m'.1⁻¹).val * X * m'.2.val) := by
  ext1
  rw [Units.val_mul, CtLevel.blk_val, CtLevel.blk_val, CtLevel.blk_val, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, fromBlocks_multiply]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
    Matrix.mul_add]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (m'.1.val) ((m'.1⁻¹ : GLw a w).val), Units.mul_inv, Matrix.one_mul]

theorem blk_one_zero {a b n : ℕ} (h : a + b = n) (w : Pl E) : blk h w 1 0 = 1 := by
  ext1
  rw [CtLevel.blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Units.val_one, Matrix.mul_zero, fromBlocks_one,
    reindex_apply, submatrix_one_equiv]
  rfl

def sM {a b n : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* parB h w where
  toFun m := ⟨blk h w m 0, blk_mem h w m 0⟩
  map_one' := Subtype.ext (blk_one_zero h w)
  map_mul' m m' := Subtype.ext (by simp [blk_mul_blk])

def uN {a b n : ℕ} (h : a + b = n) (w : Pl E) : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* parB h w where
  toFun X := ⟨blk h w 1 (Multiplicative.toAdd X), blk_mem h w 1 _⟩
  map_one' := Subtype.ext (by simpa using blk_one_zero h w)
  map_mul' X Y := Subtype.ext (by simp [blk_mul_blk, add_comm])

theorem sM_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    (sM h w m : GLw n w) = blk h w m 0 := rfl

theorem uN_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    (uN h w X : GLw n w) = blk h w 1 (Multiplicative.toAdd X) := rfl

theorem sM_mul_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    ((sM h w m * uN h w X : parB h w) : GLw n w) = blk h w m (Multiplicative.toAdd X) := by
  rw [Subgroup.coe_mul, sM_val, uN_val, blk_mul_blk]
  simp

theorem levH_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : levH h w ⟨blk h w m X, blk_mem h w m X⟩ = m := by
  have key : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ x :
        GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j = ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m x : GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [GlobalTheory.SmGL.leviProj_apply, CtLevel.blk_val]
    cases x
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
  have : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ =
      GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    funext x; exact Units.ext (Matrix.ext fun i j => key x i j)
  simp only [levH, MonoidHom.coe_comp, Function.comp_apply, this]
  simp

theorem levH_sM {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) : levH h w (sM h w m) = m :=
  levH_blk h w m 0

theorem levH_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    levH h w (uN h w X) = 1 :=
  levH_blk h w 1 _

theorem uN_injective {a b n : ℕ} (h : a + b = n) (w : Pl E) : Function.Injective (uN h w) := by
  intro X Y hXY
  have h1 := congrArg (fun p : parB h w => ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hXY
  simp only [uN_val, CtLevel.blk_val] at h1
  have h2 := congrArg (fun M => M.toBlocks₁₂) ((reindex (CtLevel.blkEq h) (CtLevel.blkEq h)).injective h1)
  simpa using h2

theorem exists_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (p : parB h w) (hp : levH h w p = 1) :
    ∃ X, uN h w X = p := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p = 1 := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) hp
    simpa [levH] using this
  have hd : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, i⟩) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, j⟩) =
        (1 : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [← GlobalTheory.SmGL.leviProj_apply, hl]
    rfl
  have h0 := (GlobalTheory.SmGL.mem_parab_two _).1 p.2
  refine ⟨Multiplicative.ofAdd
    ((((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).submatrix (CtLevel.blkEq h) (CtLevel.blkEq h)).toBlocks₁₂),
    Subtype.ext (Units.ext ?_)⟩
  rw [uN_val, CtLevel.blk_val]
  refine Matrix.ext fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [fromBlocks_apply₁₁]
    exact (hd false i j).symm
  · simp [toBlocks₁₂]
  · rw [fromBlocks_apply₂₁]
    exact (h0 i j).symm
  · rw [fromBlocks_apply₂₂]
    exact (hd true i j).symm

end GlobalTheory.LeviFubini
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBorelEqDiagonalMulUnipotent
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.UnitaryBorel

theorem borel_eq_diag_mul_unip_sameDiag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (β : GU σ n), IsBorelU β →
    ∃ t ν : GU σ n, β = t * ν ∧ IsUnipU ν ∧
      (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧
      ∀ i, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((β : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  intro L _ _ σ n b hb
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ)
    (fun i => (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)
    (Formalism.UG.P.fSatake_unit_diag hb)
  have hne : ∀ i, (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i ≠ 0 :=
    Formalism.UG.P.fSatake_ne_zero_of_borel hb
  have hu : (((d⁻¹ * b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ((((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
        (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Subgroup.coe_mul, Units.val_mul, hd']
  refine ⟨d, d⁻¹ * b, by group, ⟨fun i j hji => ?_, fun i => ?_⟩,
    fun i j hij => by rw [hd, Matrix.diagonal_apply_ne _ hij], fun i => by rw [hd, Matrix.diagonal_apply_eq]⟩
  · rw [hu, Matrix.diagonal_mul, hb i j hji, mul_zero]
  · rw [hu, Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]

end GlobalTheory.UnitaryBorel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCommutingEqMulNormOneTorus
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapTorus

theorem mul_of_comm_gen {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A)
    (hu : Algebra.adjoin K.E {u} = ⊤) (f : B.A → B.A) (hadd : ∀ y z, f (y + z) = f y + f z)
    (hsmul : ∀ (c : K.E) y, f (c • y) = c • f y) (hcomm : ∀ y, f (u * y) = u * f y) :
    ∀ y, f y = f 1 * y := by
  have key : ∀ s ∈ Algebra.adjoin K.E {u}, ∀ y, f (s * y) = s * f y := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hcomm
    | algebraMap c => intro y; rw [← Algebra.smul_def, hsmul, Algebra.smul_def]
    | add x y _ _ hx hy => intro z; rw [add_mul, hadd, hx, hy, add_mul]
    | mul x y _ _ hx hy => intro z; rw [mul_assoc, hx, hy, mul_assoc]
  intro y
  have := key y (hu ▸ Algebra.mem_top) 1
  rw [mul_one] at this
  rw [this, mul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem stdH_unitary (w : Pl E) {n : ℕ} (h : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hh : cT (cj w) h * 1 * h = 1) (v v' : Fin n → w.adicCompletion E) :
    stdH w (h *ᵥ v) (h *ᵥ v') = stdH w v v' := by
  have e1 : ∀ y y' : Fin n → w.adicCompletion E, stdH w y y' = y ⬝ᵥ (fun k => cj w (y' k)) := fun _ _ => rfl
  have hmap : (fun k => cj w ((h *ᵥ v') k)) = (h.map (cj w)) *ᵥ (fun k => cj w (v' k)) := by
    funext k
    simp [Matrix.mulVec, dotProduct, map_sum]
  have ht : hᵀ * h.map (cj w) = 1 := by
    have := congrArg Matrix.transpose hh
    simpa [cT, Matrix.transpose_mul] using this
  rw [e1, e1, hmap, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ht,
    Matrix.one_mulVec]

theorem stdH_single (w : Pl E) {n : ℕ} (v : Fin n → w.adicCompletion E) (i : Fin n) :
    stdH w v (Pi.single i 1) = v i := by
  simp [stdH, Pi.single_apply, apply_ite (cj w)]

theorem torusOf_mem_of_mem_UL_commute : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h : GLw n w, h ∈ UL n w → h * γ = γ * h → torusOf w B ψ h ∈ B.T ∧ ∀ y, ψ ((torusOf w B ψ h : B.A) * y) = h.val *ᵥ ψ y := by
  intro E _ _ _ w hw K e B Q u x n γ ψ hfit hmod h hU hc
  obtain ⟨hsm, hu, hst⟩ := hmod
  have conj : ∀ g : GLw n w, g * γ = γ * g → ∀ y, ψ.symm (g.val *ᵥ ψ y) = ψ.symm (g.val *ᵥ ψ 1) * y := by
    intro g hg
    apply mul_of_comm_gen B u hfit.1 (fun y => ψ.symm (g.val *ᵥ ψ y))
    · intro y z; simp [map_add, Matrix.mulVec_add]
    · intro c y
      apply ψ.injective
      simp only [hsm, ψ.apply_symm_apply, Matrix.mulVec_smul]
    · intro y
      apply ψ.injective
      simp only [hu, ψ.apply_symm_apply, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, ← Units.val_mul, hg]
  have hc' : h⁻¹ * γ = γ * h⁻¹ := (Commute.inv_left (show Commute h γ from hc)).eq
  set a := ψ.symm (h.val *ᵥ ψ 1) with ha_def
  set b := ψ.symm ((h⁻¹ : GLw n w).val *ᵥ ψ 1) with hb_def
  have hab : a * b = 1 := by
    rw [← conj h hc b, hb_def, ψ.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec, ψ.symm_apply_apply]
  let t : B.Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  have hspec : ∀ y, ψ ((t : B.A) * y) = h.val *ᵥ ψ y := by
    intro y
    show ψ (a * y) = _
    rw [← conj h hc y, ψ.apply_symm_apply]
  have htor : torusOf w B ψ h = t := torusOf_spec w B ψ h t hspec
  rw [htor]
  refine ⟨?_, hspec⟩

  have hUJ : cT (cj w) h.val * 1 * h.val = 1 := by
    have : h ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      unfold UL at hU; rwa [if_neg hw] at hU
    exact this
  have hinv : ∀ y z, B.herm x ((t : B.A) * y) ((t : B.A) * z) = B.herm x y z := by
    intro y z
    apply e.injective
    rw [← hst, ← hst, hspec, hspec, stdH_unitary w h.val hUJ]
  have hzero : ∀ y z, B.herm x (((t : B.A) * B.σ (t : B.A) - 1) * y) z = 0 := by
    intro y z
    have h1 : B.herm x (((t : B.A) * B.σ (t : B.A) - 1) * y) z =
        B.herm x ((t : B.A) * y) ((t : B.A) * z) - B.herm x y z := by
      unfold GlobalTheory.UnitLemma.InvAlg.herm
      rw [← map_sub]
      congr 1
      rw [map_mul]; ring
    rw [h1, hinv, sub_self]
  have hnd : ∀ m : B.A, (∀ z, B.herm x m z = 0) → m = 0 := by
    intro m hm
    apply ψ.injective
    rw [map_zero]
    funext i
    have := congrArg e (hm (ψ.symm (Pi.single i 1)))
    rw [← hst, ψ.apply_symm_apply, stdH_single, map_zero] at this
    simpa using this
  have := hnd _ (hzero 1)
  rw [mul_one, sub_eq_zero] at this
  exact this

end GlobalTheory.KapTorus
end
end

