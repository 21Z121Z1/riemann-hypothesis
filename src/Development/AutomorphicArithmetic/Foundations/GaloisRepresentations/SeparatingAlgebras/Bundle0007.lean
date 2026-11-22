import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EllGrp
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.ellGrp_pf :
    UpperTheory.Gal.Gen.EllGrp := by
  classical
  intro G H _ _ Γ C lam hyp
  have key : ∀ (r γ₁ γ₂ : G), γ₁ ∈ Γ → γ₂ ∈ Γ → ∀ c₁ c₂ : C,
      γ₁ * r * c₁ = γ₂ * r * c₂ → lam c₁ = lam c₂ := by
    intro r γ₁ γ₂ h1 h2 c₁ c₂ h
    have h' : γ₂⁻¹ * γ₁ * r = r * ((c₂ * c₁⁻¹ : C) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      calc γ₂⁻¹ * γ₁ * r = γ₂⁻¹ * (γ₁ * r * c₁) * (c₁ : G)⁻¹ := by group
        _ = γ₂⁻¹ * (γ₂ * r * c₂) * (c₁ : G)⁻¹ := by rw [h]
        _ = r * ((c₂ : G) * (c₁ : G)⁻¹) := by group
    have h3 := hyp r _ (Γ.mul_mem (Γ.inv_mem h2) h1) _ h'
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3.symm
  obtain ⟨R, hR⟩ : ∃ R : G → Set G, ∀ g x, x ∈ R g ↔ ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c :=
    ⟨fun g => {x | ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c}, fun _ _ => Iff.rfl⟩
  have hself : ∀ g, g ∈ R g := fun g => (hR g g).2 ⟨1, Γ.one_mem, 1, by simp⟩
  have hsub : ∀ g g', g' ∈ R g → R g' ⊆ R g := by
    intro g g' hg x hx
    obtain ⟨γ, hγ, c, e⟩ := (hR g g').1 hg
    obtain ⟨γ', hγ', c', e'⟩ := (hR g' x).1 hx
    exact (hR g x).2 ⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by rw [e', e, Subgroup.coe_mul]; group⟩
  have hsymm : ∀ g g', g' ∈ R g → g ∈ R g' := by
    intro g g' hg
    obtain ⟨γ, hγ, c, e⟩ := (hR g g').1 hg
    exact (hR g' g).2 ⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by rw [e, Subgroup.coe_inv]; group⟩
  obtain ⟨rep, hrep⟩ : ∃ rep : G → G, ∀ g, rep g = Classical.epsilon (· ∈ R g) :=
    ⟨_, fun _ => rfl⟩
  have hrepR : ∀ g g', g' ∈ R g → rep g' = rep g := by
    intro g g' hg
    have hRR : R g' = R g := Set.Subset.antisymm (hsub g g' hg) (hsub g' g (hsymm g g' hg))
    rw [hrep, hrep, hRR]
  have hdec : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c := by
    intro g
    have hm : rep g ∈ R g := by
      rw [hrep]
      exact Classical.epsilon_spec ⟨g, hself g⟩
    obtain ⟨γ, hγ, c, e⟩ := (hR g _).1 hm
    exact ⟨c⁻¹, γ⁻¹, Γ.inv_mem hγ, by rw [e, Subgroup.coe_inv]; group⟩
  let ℓ : G → H := fun g => lam (Classical.choose (hdec g))
  have hℓ : ∀ g γ, γ ∈ Γ → ∀ c : C, g = γ * rep g * c → ℓ g = lam c := by
    intro g γ hγ c e
    obtain ⟨γ0, h0, e0⟩ := Classical.choose_spec (hdec g)
    exact key (rep g) γ0 γ h0 hγ _ _ (e0.symm.trans e)
  refine ⟨ℓ, ?_, ?_⟩
  · intro γ hγ g
    obtain ⟨c0, γ0, h0, e0⟩ := hdec g
    have hr : rep (γ * g) = rep g := hrepR g _ ((hR g _).2 ⟨γ, hγ, 1, by simp⟩)
    rw [hℓ g γ0 h0 c0 e0]
    apply hℓ (γ * g) (γ * γ0) (Γ.mul_mem hγ h0) c0
    rw [hr]
    conv_lhs => rw [e0]
    simp only [mul_assoc]
  · intro g c
    obtain ⟨c0, γ0, h0, e0⟩ := hdec g
    have hr : rep (g * c) = rep g := hrepR g _ ((hR g _).2 ⟨1, Γ.one_mem, c, by simp⟩)
    rw [hℓ g γ0 h0 c0 e0, ← map_mul]
    apply hℓ (g * c) γ0 h0 (c0 * c)
    rw [hr, Subgroup.coe_mul]
    conv_lhs => rw [e0]
    simp only [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LevFacts
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

open GlobalTheory.Cong.LevelExt in
theorem UpperTheory.Gal.Gen.levFacts_pf :
    UpperTheory.Gal.Gen.LevFacts := by
  intro E _ _ _ a w₀ hw K hK J hJo hJc
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let s : GL (Fin a) (w₀.adicCompletion E) → UA E a := fun h => ((e.symm h : locU a w₀) : UA E a)
  have hs_mem : ∀ h, s h ∈ locU a w₀ := fun h => (e.symm h).2
  have hs_loc : ∀ h, cLoc w₀ (s h) = h := fun h => by
    rw [← he]
    exact e.apply_symm_apply h
  have hs_cont : Continuous s := continuous_subtype_val.comp e.symm.continuous
  have hs_eq : ∀ x ∈ locU a w₀, s (cLoc w₀ x) = x := fun x hx => by
    have := e.symm_apply_apply ⟨x, hx⟩
    rw [he] at this
    exact congrArg Subtype.val this
  have hcont := GlobalTheory.BCT.GlobLev.continuous_cLoc (E := E) (n := a) w₀
  have hnap : ¬ Apart w₀ w₀ := not_apart_self w₀
  have hloc : ∀ k ∈ K, ∀ x, cLoc w₀ (k * x) = cLoc w₀ x := fun k hk x => by
    rw [map_mul, hK.one k hk w₀ hnap, one_mul]
  have hnorm : ∀ J' : Subgroup (GL (Fin a) (w₀.adicCompletion E)),
      K ≤ Subgroup.normalizer ((locU a w₀ ⊓ J'.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) := by
    intro J'
    have hKL : ∀ k ∈ K, ∀ l ∈ locU a w₀ ⊓ J'.comap (cLoc w₀), k * l * k⁻¹ ∈ locU a w₀ ⊓ J'.comap (cLoc w₀) := by
      rintro k hk l ⟨hl1, hl2⟩
      have hl1' := (mem_locU_iff l).1 hl1
      refine ⟨(mem_locU_iff _).2 ⟨mul_mem (mul_mem (hK.fin hk) hl1'.1) (inv_mem (hK.fin hk)), fun u hu => ?_⟩, ?_⟩
      · simp only [map_mul, map_inv, hl1'.2 u hu, mul_one, mul_inv_cancel]
      · show cLoc w₀ (k * l * k⁻¹) ∈ J'
        simp only [map_mul, map_inv, hK.one k hk w₀ hnap, one_mul, inv_one, mul_one]
        exact hl2
    exact fun k hk => Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => hKL k hk l hl, fun hl => by
      have := hKL k⁻¹ (inv_mem hk) _ hl
      simpa [mul_assoc] using this⟩
  have hmem : ∀ (J' : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (c : UA E a),
      c ∈ lev K w₀ J' ↔ ∃ k ∈ K, ∃ x ∈ locU a w₀, cLoc w₀ x ∈ J' ∧ c = k * x := by
    intro J' c
    show c ∈ K ⊔ (locU a w₀ ⊓ J'.comap (cLoc w₀)) ↔ _
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J'), Set.mem_mul]
    constructor
    · rintro ⟨k, hk, x, hx, rfl⟩
      exact ⟨k, hk, x, hx.1, hx.2, rfl⟩
    · rintro ⟨k, hk, x, hx, hxJ, rfl⟩
      exact ⟨k, hk, x, ⟨hx, hxJ⟩, rfl⟩
  have hJmem : ∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J := by
    intro c hc
    obtain ⟨k, hk, x, -, hxJ, rfl⟩ := (hmem J c).1 hc
    rwa [hloc k hk]
  have hLc : IsCompact ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) := by
    have : ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) = s '' (J : Set _) := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨cLoc w₀ x, hx2, hs_eq x hx1⟩
      · rintro ⟨h, hh, rfl⟩
        refine ⟨hs_mem h, ?_⟩
        show cLoc w₀ (s h) ∈ J
        rw [hs_loc]
        exact hh
    rw [this]
    exact hJc.image hs_cont
  refine ⟨⟨sup_le hK.fin (fun x hx => ((mem_locU_iff x).1 (Subgroup.mem_inf.1 hx).1).1), ?_, ?_⟩, hmem J, hJmem,
    ?_, fun y => ⟨s y, hs_mem y, hs_loc y⟩, ?_⟩
  · show IsCompact ((K ⊔ (locU a w₀ ⊓ J.comap (cLoc w₀)) : Subgroup (UA E a)) : Set (UA E a))
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J)]
    exact hK.compact.mul hLc
  · obtain ⟨N₀, hN₀o, hN₀1, hN₀⟩ := hK.isOpen
    let k : UA E a → UA E a := fun x => x * (s (cLoc w₀ x))⁻¹
    have hkc : Continuous k := continuous_id.mul ((hs_cont.comp hcont).inv)
    have hs1 : s 1 = 1 := by
      have := hs_eq 1 (one_mem _)
      rwa [map_one] at this
    refine ⟨k ⁻¹' N₀ ∩ cLoc w₀ ⁻¹' (J : Set _), (hN₀o.preimage hkc).inter (hJo.preimage hcont), ⟨?_, ?_⟩, ?_⟩
    · show k 1 ∈ N₀
      have : k 1 = 1 := by simp [k, hs1]
      rw [this]
      exact hN₀1
    · show cLoc w₀ 1 ∈ J
      rw [map_one]
      exact J.one_mem
    · rintro x ⟨⟨hxN, hxJ⟩, hxf⟩
      have hkx : k x ∈ K := by
        refine hN₀ _ hxN ?_ ?_
        · exact mul_mem hxf (inv_mem ((mem_locU_iff _).1 (hs_mem _)).1)
        · exact one_of_cLoc hw _ (by simp only [k, map_mul, map_inv, hs_loc, mul_inv_cancel])
      refine (hmem J x).2 ⟨k x, hkx, s (cLoc w₀ x), hs_mem _, ?_, by simp [k]⟩
      rw [hs_loc]
      exact hxJ
  · intro c hc h1
    obtain ⟨k, hk, x, hx, -, rfl⟩ := (hmem J c).1 hc
    rw [hloc k hk] at h1
    have hx1 : x = 1 := by
      have h2 := hs_eq x hx
      have hs1 : s 1 = 1 := by
        have := hs_eq 1 (one_mem _)
        rwa [map_one] at this
      rw [h1, hs1] at h2
      exact h2.symm
    rw [hx1, mul_one]
    exact hk
  · intro J' c hc hcJ'
    obtain ⟨k, hk, x, hx, -, rfl⟩ := (hmem J c).1 hc
    rw [hloc k hk] at hcJ'
    exact (hmem J' _).2 ⟨k, hk, x, hx, hcJ', rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LocComm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.locComm_pf :
    UpperTheory.Gal.Gen.LocComm := by
  intro E _ _ _ a w₀ x g hx hg
  obtain ⟨hxf, hxa⟩ := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  have hxi : cInf x = 1 := hxf
  refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)
  · change cInf (x * g) = cInf (g * x)
    rw [map_mul, map_mul, hxi, one_mul, mul_one]
  · change cLoc u (x * g) = cLoc u (g * x)
    rw [map_mul, map_mul]
    by_cases hu : Apart u w₀
    · rw [hxa u hu, one_mul, mul_one]
    · rw [hg u hu, one_mul, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NeglAt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.neglAt_pf :
    UpperTheory.Gal.Gen.GlobOp → UpperTheory.Gal.Gen.Small → UpperTheory.Gal.Gen.NeglAt := by
  intro hG hS E _ _ _ a K w₀ w hs hap hyp Φ hΦ δ hδ
  obtain ⟨C, hC⟩ := hG E a K w hs hyp
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨p, hp, hp1, hI⟩ := hS a Φ hΦ (δ / (|C| + 1)) (div_pos hδ hC1)
  obtain ⟨h, hloc, hsep, hnorm, hop⟩ := hC p hp
  refine ⟨h, ?_, hsep, ?_, ?_⟩
  · intro g hg
    have hm := (GlobalTheory.Cong.LevelExt.mem_locU_iff g).1 (hloc g hg)
    refine ⟨hm.1, fun u hu => hm.2 u ?_⟩
    have e : u.under (𝓞 (maximalRealSubfield E)) = w₀.under (𝓞 (maximalRealSubfield E)) :=
      Classical.byContradiction hu
    intro e'
    exact hap (e'.symm.trans e)
  · have hI0 : 0 ≤ ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    calc ∑ g ∈ h.support, ‖h g‖ ^ 2
        ≤ C * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 := hnorm
      _ ≤ |C| * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hI0
      _ ≤ |C| * (δ / (|C| + 1)) := mul_le_mul_of_nonneg_left hI (abs_nonneg C)
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ hC1]
          nlinarith [abs_nonneg C]
  · intro U hU hB φ hφ hfix
    have hB' : ¬ GenAt w Φ U := hB
    unfold GenAt at hB'
    push_neg at hB'
    obtain ⟨z, hz, h0⟩ := hB'
    rw [hop U hU z hz φ hφ hfix, hp1 z h0, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.OpOfFinsetSum
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem opOf_finset_sum {Γ V ι : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    (f : Γ →₀ ℂ) (I : Finset ι) (u : ι → V) : opOf ρ f (∑ i ∈ I, u i) = ∑ i ∈ I, opOf ρ f (u i) := by
  unfold opOf
  simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

private theorem finite_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Subgroup G}
    (hA : IsCompact (A : Set G)) (hB : IsOpen (B : Set G)) : Finite (A ⧸ B.subgroupOf A) := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA
  have ho : IsOpen ((B.subgroupOf A : Subgroup A) : Set A) := hB.preimage continuous_subtype_val
  exact Subgroup.quotient_finite_of_isOpen _ ho

private theorem bound_arith {M s ε c t : ℝ} (hM : 0 ≤ M) (hs : 0 ≤ s) (hε : 0 < ε) (hc : 0 ≤ c) (ht : t ≤ ε / (M * s + 1)) :
    M * (s * c) * t ≤ ε * c := by
  have hd : 0 < M * s + 1 := by positivity
  have h1 : M * s * t ≤ ε := by
    have hMs : 0 ≤ M * s := by positivity
    calc M * s * t ≤ M * s * (ε / (M * s + 1)) := mul_le_mul_of_nonneg_left ht hMs
      _ = ε * (M * s / (M * s + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one hd).2 (by linarith)) hε.le
      _ = ε := mul_one ε
  calc M * (s * c) * t = (M * s * t) * c := by ring
    _ ≤ ε * c := mul_le_mul_of_nonneg_right h1 hc

theorem UpperTheory.Gal.Gen.count_pf :
    UpperTheory.Gal.Gen.CountCore → UpperTheory.Gal.Gen.Cover → UpperTheory.Gal.Gen.Sep → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.Count := by
  intro hCore hCover hSep hPart E _ _ _ a w₀ hs K hK J hJ W B hB ε hε
  obtain ⟨M, hM0, hM⟩ := hCore E a W
  obtain ⟨S, hS⟩ := hCover E a w₀ hs K hK J hJ
  have hδ : 0 < ε / (M * (S.card : ℝ) + 1) := by positivity
  obtain ⟨h, h1, h2, h3, h4⟩ := hB _ hδ
  obtain ⟨n₀, hn₀⟩ := hSep E a w₀ hs K hK J hJ S h.support h1 h2
  refine ⟨n₀, fun n hn => ?_⟩
  haveI : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) := finite_quot (hJ.compact 0) (hJ.isOpen n)
  letI : Fintype (J 0 ⧸ (J n).subgroupOf (J 0)) := Fintype.ofFinite _
  obtain ⟨r, hr, hcov⟩ := hS n
  have hsep : Separates (lev K w₀ (J n)) (fun y : S × (J 0 ⧸ (J n).subgroupOf (J 0)) => y.1.1 * r y.2) h.support :=
    fun y g hg g' hg' γ hγ x hx c hc e =>
      hn₀ n hn (y.1, ⟨r y.2, hr y.2⟩) g hg g' hg' γ hγ x hx c hc e
  have hfix : ∀ f ∈ part W (lev K w₀ (J n)) B, ∀ v, opOf (RU E a) h (f.1 v) = f.1 v := by
    intro f hf v
    obtain ⟨I, F, hF, rfl⟩ := (hPart E a W (lev K w₀ (J n)) B).2.2.2.2 f hf
    have e : (∑ π ∈ I, F π : algForms W).1 v = ∑ π ∈ I, (F π).1 v := by
      simp [Submodule.coe_sum, LinearMap.sum_apply]
    rw [e, opOf_finset_sum]
    refine Finset.sum_congr rfl fun π hπ => ?_
    obtain ⟨hP, hfin, hfx, -⟩ := hF π hπ
    refine h4 π.V π.isAut hP _ (AutSub.mem_finPart.1 hfin v) fun x hx => funext fun g => ?_
    rw [RU_apply]
    exact hfx x ((le_sup_left : K ≤ lev K w₀ (J n)) hx) v g
  obtain ⟨hfd, hle⟩ := hM (lev K w₀ (J n)) _ _ hcov h hsep (part W (lev K w₀ (J n)) B)
    (hPart E a W (lev K w₀ (J n)) B).2.1 hfix
  refine ⟨hfd, hle.trans ?_⟩
  have hcard : (Fintype.card (S × (J 0 ⧸ (J n).subgroupOf (J 0))) : ℝ) =
      (S.card : ℝ) * (Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_coe, Nat.card_eq_fintype_card]
    push_cast
    rfl
  rw [hcard]
  exact bound_arith hM0 (Nat.cast_nonneg _) hε (Nat.cast_nonneg _) h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RatFin
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.ratFin_pf :
    UpperTheory.Gal.Gen.RatFin := by
  intro E _ _ _ a
  refine ⟨?_, ?_⟩
  · intro Z hZ
    haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
    have hcl : IsClosed (((ratGL E a).range : Subgroup (GA E a)) : Set (GA E a)) := Subgroup.isClosed_of_discrete
    let K : Set (GA E a) := Subtype.val '' Z
    have hK : IsCompact K := hZ.image continuous_subtype_val
    have hKG : IsCompact (K ∩ ((ratGL E a).range : Set (GA E a))) := hK.inter_right hcl
    let t : Set (ratGL E a).range := {x | (x : GA E a) ∈ K}
    have himg : Subtype.val '' t = K ∩ ((ratGL E a).range : Set (GA E a)) := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
      · rintro ⟨hy, hy'⟩; exact ⟨⟨y, hy'⟩, hy, rfl⟩
    have ht : IsCompact t := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]; exact hKG
    have hfin : (K ∩ ((ratGL E a).range : Set (GA E a))).Finite := by
      rw [← himg]; exact (ht.finite_of_discrete).image _
    refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨x, ⟨hxZ, hxr⟩, rfl⟩
    exact ⟨⟨x, hxZ, rfl⟩, (Subgroup.mem_subgroupOf).1 hxr⟩
  · intro w γ hγ h1
    obtain ⟨δ, hδ⟩ := (Subgroup.mem_subgroupOf).1 hγ
    have hδ1 : δ = 1 := by
      ext i j
      have h2 := congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.1 i j) h1
      have h3 : (cLoc w γ : GL (Fin a) (w.adicCompletion E)).1 i j = algebraMap E (w.adicCompletion E) (δ.1 i j) := by
        simp [cLoc, ← hδ, pLoc, pFin, ratGL]
        rfl
      have h4 : algebraMap E (w.adicCompletion E) (δ.1 i j) =
          algebraMap E (w.adicCompletion E) ((1 : GL (Fin a) E).1 i j) := by
        rw [← h3]
        refine h2.trans ?_
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      exact (algebraMap E (w.adicCompletion E)).injective h4
    apply Subtype.ext
    rw [← hδ, hδ1, map_one]; rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Restrict
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.restrict_pf :
    UpperTheory.Gal.Gen.Restrict := by
  classical
  intro k _ _ J J' i θ S h ε hε
  obtain ⟨s, c, hs, hc⟩ := h ε hε
  refine ⟨s.image (fun x => x ∘ i), fun ζ => ∑ η ∈ s with η ∘ i = ζ, c η, ?_, ?_⟩
  · intro ζ hζ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hζ
    obtain ⟨η, hη, rfl⟩ := hζ
    exact ⟨η, hs hη, rfl⟩
  · intro P
    have key : ∀ η : J' → k,
        MvPolynomial.aeval (η ∘ i) P = MvPolynomial.aeval η (MvPolynomial.rename i P) := by
      intro η
      rw [MvPolynomial.aeval_rename]
    calc _ = ‖MvPolynomial.aeval θ (MvPolynomial.rename i P)
          - ∑ η ∈ s, c η * MvPolynomial.aeval η (MvPolynomial.rename i P)‖ := by
          congr 2
          · exact key θ
          · rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image (fun x => x ∘ i))
              (g := fun x => x ∘ i) (fun η hη => Finset.mem_image_of_mem _ hη)]
            refine Finset.sum_congr rfl fun ζ _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun η hη => ?_
            rw [← (Finset.mem_filter.1 hη).2, key]
      _ ≤ ε := hc _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SmoothAt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.smoothAt_pf :
    UpperTheory.Gal.Gen.SmoothAt := by
  intro E _ _ _ a w₀ hw W f
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let p : GL (Fin a) (w₀.adicCompletion E) → finU E a := fun y =>
    ⟨(e.symm y).1, (Subgroup.mem_inf.1 (e.symm y).2).1⟩
  have hp : Continuous p :=
    Continuous.subtype_mk (continuous_subtype_val.comp e.symm.continuous) _
  have hp1 : p 1 = 1 := by
    apply Subtype.ext
    simp [p]
  have hS : IsOpen {k : finU E a | algRep W k f = f} := GlobalTheory.DefU.isSmooth_algRep W f
  refine ⟨p ⁻¹' {k : finU E a | algRep W k f = f},
    (hS.preimage hp).mem_nhds (by simp [hp1]), fun x hx hxN v g => ?_⟩
  have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
    rw [← he ⟨x, hx⟩]
    exact e.symm_apply_apply _
  have h2 : algRep W (p (cLoc w₀ x)) f = f := hxN
  have h3 : (p (cLoc w₀ x)).1 = x := by
    simp only [p, h1]
  have h4 := congrArg (fun F : algForms W => F.1 v g) h2
  change f.1 v (g * (p (cLoc w₀ x)).1) = f.1 v g at h4
  rwa [h3] at h4
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StepCore
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.stepCore_pf :
    UpperTheory.Gal.Gen.AlgC → UpperTheory.Gal.Gen.Codim → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.StepCore := by
  intro hAlg hCod hPF E _ _ _ l _ ι a W C C' hCfin H _ _ hH lam hsurj hC'C hker ℓ hinf hright haut P hfd hcard f hf
  letI : Fintype H := Fintype.ofFinite H
  have hex : ∀ φ : H → ℂ, ∃ F : algForms W, ∀ v g, F.1 v g = φ (ℓ g) * f.1 v g := fun φ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => φ (ℓ g)) (haut φ) (fun g x hx => by simp only [hinf g x hx])
  choose Ψ₀ hΨ₀ using hex
  let Ψ : (H → ℂ) →ₗ[ℂ] algForms W :=
    { toFun := Ψ₀
      map_add' := fun φ ψ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply, hΨ₀]
        ring
      map_smul' := fun c φ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, hΨ₀, RingHom.id_apply, smul_eq_mul]
        ring }
  have hΨ : ∀ φ v g, (Ψ φ).1 v g = φ (ℓ g) * f.1 v g := hΨ₀
  have hfix : ∀ φ, Ψ φ ∈ fixedBy W C' := fun φ k hk v g => by
    have hkC : k ∈ C := hC'C hk
    have h1 : lam ⟨k, hkC⟩ = 1 := (hker ⟨k, hkC⟩).1 hk
    have h2 : ℓ (g * k) = ℓ g := by
      have := hright g ⟨k, hkC⟩
      rw [h1, mul_one] at this
      exact this
    rw [hΨ, hΨ, h2, hf k hkC v g]
  obtain ⟨h1, -, -, h4, -⟩ := hPF E a W C' P
  have hdim := hCod ℂ (H → ℂ) (algForms W) Ψ (part W C' P) (part W C' fun U => ¬ P U) (fun φ => h1 (hfix φ))
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  rw [Nat.card_eq_fintype_card] at hcard
  have hA : Fintype.card H ≤ 2 * Module.finrank ℂ ((part W C' P).comap Ψ) := by omega
  have hstable : ∀ c ∈ (part W C' P).comap Ψ, ∀ u, (fun h => c (h * u)) ∈ (part W C' P).comap Ψ := by
    intro φ hφ u
    obtain ⟨c, rfl⟩ := hsurj u
    have hnorm : ∀ c' ∈ C', (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C' := by
      intro c' hc'
      have hc'C : c' ∈ C := hC'C hc'
      have hm : (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C := C.mul_mem (C.mul_mem (C.inv_mem c.2) hc'C) c.2
      refine (hker ⟨_, hm⟩).2 ?_
      have e1 : (⟨_, hm⟩ : C) = c⁻¹ * ⟨c', hc'C⟩ * c := Subtype.ext rfl
      rw [e1, map_mul, map_mul, (hker ⟨c', hc'C⟩).1 hc', mul_one, map_inv, inv_mul_cancel]
    have hrep : Ψ (fun h => φ (h * lam c)) = algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ) :=
      Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        have e2 : (algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ)).1 v g = (Ψ φ).1 v (g * c.1) := rfl
        rw [e2, hΨ, hΨ, hright g c, hf c.1 c.2 v g]
    change Ψ _ ∈ part W C' P
    rw [hrep]
    exact h4 ⟨c.1, hCfin c.2⟩ hnorm _ hφ
  obtain ⟨φ, hφ, hnorm⟩ := hAlg l ι H hH _ hstable hA
  exact ⟨Ψ φ, hφ, fun g => 1 - φ (ℓ g), fun g => hnorm (ℓ g), fun v g => by rw [hΨ]; ring⟩
end

