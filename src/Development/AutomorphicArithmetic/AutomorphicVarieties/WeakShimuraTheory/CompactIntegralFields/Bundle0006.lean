import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem charP_res (c : Coef l) : CharP (ResidueField c.O) l := by
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, hloc, -, -, he, -, hval, -⟩ := dvrFacts l c.O
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
  have hmem : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 : IsDiscreteValuationRing.addVal c.O (l : c.O) = 0 :=
      (IsDiscreteValuationRing.addVal_eq_zero_iff).2 hu
    exact he (hval.trans h0)
  have := (residue_eq_zero_iff ((l : ℕ) : c.O)).2 hmem
  simpa using this

private theorem pow_inj {x y : ResidueField c.O} (j : ℕ) (h : x ^ l ^ j = y ^ l ^ j) : x = y := by
  haveI := charP_res c
  haveI : ExpChar (ResidueField c.O) l := ExpChar.prime Fact.out
  induction j with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply frobenius_inj (ResidueField c.O) l
    simpa [frobenius_def, pow_succ, pow_mul] using h

private theorem pow_one_inj {x : ResidueField c.O} (j : ℕ) (h : x ^ l ^ j = 1) : x = 1 := by
  exact pow_inj j (by simpa using h)

private theorem resQ_mem (F : IntermediateField ℚ Ω) (g : G F Ω) : resQ F g ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact fun x hx => g.commutes ⟨x, hx⟩

private theorem dec_resLe {F F' : IntermediateField ℚ Ω} (h : F ≤ F') (A : ValuationSubring Ω) (g : G F' Ω) :
    resLe h g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A := Iff.rfl

private theorem ine_resLe {F F' : IntermediateField ℚ Ω} [NumberField F] [NumberField F'] (h : F ≤ F')
    (A : ValuationSubring Ω) (g : G F' Ω) :
    resLe h g ∈ Ine (F := F) A ↔ g ∈ Ine (F := F') A := Iff.rfl

variable {T T' : Tower D}

private theorem up (h : T.Le T') : ∃ j : ℕ, ∀ g : G T.F Ω, ∃ g' : G T'.F Ω, resLe h.le g' = g ^ l ^ j := by
  obtain ⟨j, hj⟩ := h.pow
  refine ⟨j, fun g => ?_⟩
  have hm := hj _ (resQ_mem T.F g)
  refine ⟨IntermediateField.fixingSubgroupEquiv T'.F ⟨_, hm⟩, ?_⟩
  ext x
  simp [resLe, IntermediateField.fixingSubgroupEquiv, map_pow]

private theorem rb_resLe (h : T.Le T') (w : ℤ × ℤ) (g : G T'.F Ω) : T'.rb w g = T.rb w (resLe h.le g) := by
  simp only [Tower.rb, Tower.fr, Fr.rt, h.pr]
  rfl

private theorem rb_pow (w : ℤ × ℤ) (g : G T.F Ω) (n : ℕ) : T.rb w (g ^ n) = T.rb w g ^ n := by
  simp only [Tower.rb, map_pow, Units.val_pow_eq_pow_val]

private theorem bar_pow (γ : G ℚ Ω →* c.Oˣ) (g : G ℚ Ω) (n : ℕ) : Raw.bar γ (g ^ n) = Raw.bar γ g ^ n := by
  simp only [Raw.bar, map_pow, Units.val_pow_eq_pow_val]

private theorem galL_resLe (h : T.Le T') (g : G T'.F Ω) : resLe h.le g ∈ T.GalL ↔ g ∈ T'.GalL := by
  simp only [Tower.GalL, Subgroup.mem_comap, h.K]
  rfl

private theorem g3'_up (hl : l ≠ 2) (h : T.Le T') (ho : T.Ok) (η : T'.GalL →* (ResidueField c.O)ˣ) (h2 : η ^ 2 = 1)
    (hom : ∀ g : T'.GalL, D.om (resQ T'.F g) = 1 → η g = 1)
    (hperm : ∀ i, ∃ j, ∀ g : T'.GalL, η g * Raw.bar (chi D T'.pr i) (resQ T'.F g) =
      Raw.bar (chi D T'.pr j) (resQ T'.F g)) : η = 1 := by
  obtain ⟨k, hk⟩ := up h
  have L : ∀ u : (ResidueField c.O)ˣ, u ^ l ^ k = 1 → u = 1 := fun u hu =>
    Units.ext (pow_one_inj k (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]))
  let φ : Fin 4 → T.GalL →* (ResidueField c.O)ˣ := fun m =>
    (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T.F).comp T.GalL.subtype))
  let φ' : Fin 4 → T'.GalL →* (ResidueField c.O)ˣ := fun m =>
    (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T'.F).comp T'.GalL.subtype))
  have hφ : ∀ m (g : T'.GalL), φ m ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩ = φ' m g := fun _ _ => rfl
  have hperm' : ∀ i, ∃ j, ∀ g : T'.GalL, η g * φ' i g = φ' j g := by
    intro i
    obtain ⟨j, hj⟩ := hperm i
    refine ⟨j, fun g => Units.ext ?_⟩
    have hj' := hj g
    rw [h.pr] at hj'
    simpa [φ', Raw.bar] using hj'
  have lift : ∀ g : T.GalL, ∃ g' : T'.GalL, ∀ m, φ m g ^ l ^ k = φ' m g' ∧
      (D.om (resQ T.F g) = 1 → D.om (resQ T'.F g') = 1) := by
    intro g
    obtain ⟨g', hg'⟩ := hk g
    have hm : g' ∈ T'.GalL := (galL_resLe h g').1 (by rw [hg']; exact pow_mem g.2 _)
    refine ⟨⟨g', hm⟩, fun m => ⟨?_, fun h1 => ?_⟩⟩
    · rw [← map_pow, ← hφ]
      congr 1
      exact Subtype.ext (by simp [hg'])
    · show D.om (resQ T.F (resLe h.le g')) = 1
      rw [hg', map_pow, map_pow, h1, one_pow]
  obtain ⟨j, hj⟩ := hperm' 0
  have hη : ∀ g : T'.GalL, η g = φ' j g / φ' 0 g := fun g => eq_div_iff_mul_eq'.2 (hj g)
  let η₀ : T.GalL →* (ResidueField c.O)ˣ := φ j / φ 0
  have hη₀ : ∀ g, η₀ g = φ j g / φ 0 g := fun _ => rfl
  have C : ∀ (g : T.GalL) (g' : T'.GalL), (∀ m, φ m g ^ l ^ k = φ' m g') → η₀ g ^ l ^ k = η g' := by
    intro g g' hm
    rw [hη g', ← hm j, ← hm 0, hη₀, div_pow]
  have h0 : η₀ = 1 := by
    refine ho.g3' η₀ ?_ ?_ ?_
    · refine MonoidHom.ext fun g => ?_
      obtain ⟨g', hg'⟩ := lift g
      rw [MonoidHom.one_apply, MonoidHom.pow_apply]
      apply L
      rw [← pow_mul, mul_comm, pow_mul, C g g' (fun m => (hg' m).1), ← MonoidHom.pow_apply, h2,
        MonoidHom.one_apply]
    · intro g hg
      obtain ⟨g', hg'⟩ := lift g
      apply L
      rw [C g g' (fun m => (hg' m).1)]
      exact hom g' ((hg' 0).2 hg)
    · intro i
      obtain ⟨i', hi'⟩ := hperm' i
      refine ⟨i', fun g => ?_⟩
      have key : η₀ g * φ i g = φ i' g := by
        obtain ⟨g', hg'⟩ := lift g
        have hu : η₀ g * φ i g / φ i' g = 1 := by
          apply L
          rw [div_pow, mul_pow, C g g' (fun m => (hg' m).1), (hg' i).1, (hg' i').1, hi' g', div_self']
        exact div_eq_one.1 hu
      have := congrArg Units.val key
      simpa [φ, Raw.bar] using this
  refine MonoidHom.ext fun g => ?_
  rw [hη g, MonoidHom.one_apply, div_eq_one, ← hφ, ← hφ]
  have := congrArg (fun f : T.GalL →* (ResidueField c.O)ˣ => f ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩) h0
  simp only [hη₀, MonoidHom.one_apply, div_eq_one] at this
  exact this

private theorem ok_up (hl : l ≠ 2) (h : T.Le T') (ho : T.Ok) : T'.Ok := by
  obtain ⟨k, hk⟩ := up h
  have L1 : ∀ x : ResidueField c.O, x ^ l ^ k = 1 → x = 1 := fun x hx => pow_one_inj k hx
  have liftL : ∀ g ∈ T.GalL, ∃ g' ∈ T'.GalL, resLe h.le g' = g ^ l ^ k := fun g hg => by
    obtain ⟨g', hg'⟩ := hk g
    exact ⟨g', (galL_resLe h g').1 (by rw [hg']; exact pow_mem hg _), hg'⟩
  refine
    { lab := ?_, even := ?_, unr := ?_, split := ?_, g2 := ?_, g3 := ?_, g3' := ?_, ord := ?_,
      kb := ?_, kc := ?_, ineL := ?_, dist := ?_, locL := ?_ }
  · rw [h.pr]
    exact ho.lab
  · obtain ⟨n, hn⟩ := IntermediateField.finrank_dvd_of_le_right h.le
    show Even (Module.finrank ℚ T'.F)
    rw [hn]
    exact (show Even (Module.finrank ℚ T.F) from ho.even).mul_right n
  · intro A g hg
    exact (galL_resLe h g).1 (ho.unr A ((ine_resLe h.le A g).2 hg))
  · intro p hp A hA
    rw [h.K]
    exact ho.split p hp A hA
  · intro w
    obtain ⟨g, hg, hne⟩ := ho.g2 w
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    refine ⟨g', hm, fun heq => hne (pow_inj k ?_)⟩
    rw [← rb_pow, ← bar_pow, ← map_pow (resQ T.F), ← hg', ← rb_resLe h]
    exact heq
  · intro w hw
    obtain ⟨g, hg, hne⟩ := ho.g3 w hw
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    exact ⟨g', hm, fun heq => hne (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))⟩
  · exact fun η h2 hom hperm => g3'_up hl h ho η h2 hom hperm
  · obtain ⟨w, hw, hord⟩ := ho.ord
    refine ⟨w, hw, fun n hn0 hn4 => ?_⟩
    obtain ⟨g, hg, hne⟩ := hord n hn0 hn4
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    refine ⟨g', hm, fun heq => hne (L1 _ ?_)⟩
    rw [← pow_mul, mul_comm, pow_mul, ← rb_pow, ← hg', ← rb_resLe h]
    exact heq
  · intro A hA g hg h1
    exact ho.kb A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg) h1
  · obtain ⟨m, hm, hψ⟩ := ho.kc
    exact ⟨m, hm, fun g hg => hψ (resLe h.le g) hg⟩
  · intro A hA g hg
    exact ho.ineL A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg)
  · intro i j hij heq
    apply ho.dist i j hij
    obtain ⟨k', hk'⟩ := h.g0
    apply pow_inj k'
    rw [← bar_pow, ← bar_pow, ← hk']
    rw [h.pr] at heq
    exact heq
  · intro A hA
    rcases ho.locL A hA with ⟨g, hg, hne⟩ | ⟨g, hg, h1, h2, h3⟩
    · obtain ⟨g', hg'⟩ := hk g
      left
      refine ⟨g', (ine_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), fun heq => hne (L1 _ ?_)⟩
      rw [← bar_pow, ← map_pow (resQ T.F), ← hg']
      exact heq
    · obtain ⟨g', hg'⟩ := hk g
      right
      refine ⟨g', (dec_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), ?_, ?_, ?_⟩
      · rw [show resQ T'.F g' = resQ T.F (resLe h.le g') from rfl, hg', map_pow, bar_pow, h1, one_pow]
      · rw [rb_resLe h, hg', rb_pow, h2, one_pow]
      · exact fun heq => h3 (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))

private theorem two_up (h : T.Le T') (ht : T.Two) : T'.Two := by
  obtain ⟨j, hj⟩ := up h
  refine ⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ?_, ht.ord, ht.xi, fun A hA => ?_, fun A hA => ?_⟩
  · rw [rb_resLe h]
    exact ht.sq _
  · rw [rb_resLe h]
    exact ht.unr A _ hg
  · rw [rb_resLe h]
    exact ht.atL A hA _ hg
  · obtain ⟨k₀, h1, h2, h3, h4⟩ := ht.quad
    refine ⟨k₀, h1, h2, h3, fun g => ?_⟩
    rw [rb_resLe h]
    exact h4 _
  · obtain ⟨g, hg, hne⟩ := ht.bigL A hA
    obtain ⟨g', hg'⟩ := hj g
    refine ⟨g', (dec_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩
    rwa [rb_resLe h, hg', rb_pow, pow_right_comm] at he
  · obtain ⟨g, hg, hne⟩ := ht.big2 A hA
    obtain ⟨g', hg'⟩ := hj g
    refine ⟨g', (ine_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩
    rwa [rb_resLe h, hg', rb_pow, pow_right_comm] at he

private theorem three_up (h : T.Le T') (ht : T.Three) : T'.Three :=
  ⟨ht.five, ht.sb, ht.psi, fun g => by rw [rb_resLe h, rb_resLe h]; exact ht.sq _⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.leFit :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T T' : Tower D, T.Le T' → (T.Ok → T'.Ok) ∧ (T.Two → T'.Two) ∧ (T.Three → T'.Three) ∧ (T.Deep → T'.Deep) ∧ (T.Fit → T'.Fit) ∧
      T.Le T ∧ ∀ T'' : Tower D, T'.Le T'' → T.Le T'' := by
  intro Ω _ _ _ l _ c D hD T T' h
  refine ⟨ok_up hD.l_odd h, two_up h, three_up h, ?_, ?_, ⟨rfl, rfl, le_rfl, ⟨0, fun g hg => by simpa using hg⟩, ⟨0, by simp⟩⟩,
    fun T'' h' => ⟨h'.pr.trans h.pr, h'.K.trans h.K, h.le.trans h'.le, ?_, ?_⟩⟩
  · rintro ⟨m, hm, hk⟩
    exact ⟨m, hm, fun g => hk (resLe h.le g)⟩
  · rintro ⟨ho, hc⟩
    exact ⟨ok_up hD.l_odd h ho, hc.imp (fun a => ⟨a.1, two_up h a.2⟩) fun a => ⟨a.1, a.2.five, a.2.sb, a.2.psi⟩⟩
  · obtain ⟨j, hj⟩ := h.pow
    obtain ⟨k, hk⟩ := h'.pow
    exact ⟨j + k, fun g hg => by rw [pow_add, pow_mul]; exact hk _ (hj g hg)⟩
  · obtain ⟨j, hj⟩ := h.g0
    obtain ⟨k, hk⟩ := h'.g0
    exact ⟨j + k, by rw [hk, hj, pow_add, pow_mul]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem fin_quot (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] (n : ℕ) (h : Module.rank A B ≤ n) :
    Module.Finite A (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) := by
  classical
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hnzd : ∀ (c : A) (x : B), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc hx
    rw [Algebra.smul_def] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd ((map_eq_zero_iff _ hinj).mp h) hc
    · exact h
  have hbound : ∀ s : Finset (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)),
      LinearIndependent (A ⧸ maximalIdeal A) (fun i : s => (i : B ⧸ (maximalIdeal A • ⊤ : Submodule A B))) →
      s.card ≤ n := by
    intro s hs
    have hlift : ∀ i : s, ∃ b : B,
        Submodule.Quotient.mk (p := (maximalIdeal A • ⊤ : Submodule A B)) b = (i : B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) :=
      fun i => Submodule.Quotient.mk_surjective _ _
    choose b hb using hlift
    have hli : LinearIndependent A b := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      by_contra hne
      push_neg at hne
      obtain ⟨i0, hi0⟩ := hne
      obtain ⟨j, hj, hjmin⟩ := (Finset.univ.filter (fun i => c i ≠ 0)).exists_min_image
        (fun i => IsDiscreteValuationRing.addVal A (c i)) ⟨i0, by simpa using hi0⟩
      have hcj : c j ≠ 0 := by simpa using hj
      have hdvd : ∀ i, c j ∣ c i := by
        intro i
        by_cases hci : c i = 0
        · rw [hci]; exact dvd_zero _
        · exact IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hjmin i (by simpa using hci))
      choose d hd using hdvd
      have hsum : c j • ∑ i, d i • b i = 0 := by
        rw [Finset.smul_sum]
        simp_rw [smul_smul, ← hd]
        exact hc
      have hsum' : ∑ i, d i • b i = 0 := hnzd _ _ hcj hsum
      have hdj : d j = 1 := by
        have h1 : c j * d j = c j * 1 := by rw [mul_one, ← hd j]
        exact mul_left_cancel₀ hcj h1
      have hk : ∑ i, Ideal.Quotient.mk (maximalIdeal A) (d i) •
          (i : B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) = 0 := by
        have h2 := congrArg (Submodule.mkQ (maximalIdeal A • ⊤ : Submodule A B)) hsum'
        simp only [map_sum, map_zero, map_smul, Submodule.mkQ_apply] at h2
        rw [← h2]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hb i]
        rfl
      have h3 := Fintype.linearIndependent_iff.mp hs _ hk j
      rw [hdj, map_one] at h3
      exact one_ne_zero h3
    have h4 := hli.cardinal_le_rank
    rw [Cardinal.mk_coe_finset] at h4
    exact_mod_cast h4.trans h
  have hrank : Module.rank (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) ≤ n :=
    rank_le hbound
  haveI : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) :=
    Module.rank_lt_aleph0_iff.mp (hrank.trans_lt (Cardinal.nat_lt_aleph0 n))
  exact Module.Finite.trans (A ⧸ maximalIdeal A) _

private theorem haus (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] [Algebra.IsAlgebraic A B] :
    IsHausdorff (maximalIdeal A) B := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  refine ⟨fun x hx => ?_⟩
  by_contra hx0
  have hmem : ∀ n : ℕ, ∃ b : B, algebraMap A B (ϖ ^ n) * b = x := by
    intro n
    have h1 := (SModEq.zero).mp (hx n)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, by rw [← hb, Algebra.smul_def]⟩
  have hne := Ideal.comap_ne_bot_of_algebraic_mem hx0 (Ideal.mem_span_singleton_self x)
    (Algebra.IsAlgebraic.isAlgebraic (R := A) x)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, hc⟩ := ha
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨b, hb⟩ := hmem (k + 1)
  have e : algebraMap A B (ϖ ^ k) * algebraMap A B (u : A)
      = algebraMap A B (ϖ ^ k) * (algebraMap A B ϖ * (b * c)) := by
    rw [← map_mul, mul_comm (ϖ ^ k), ← hu, ← hc, ← hb, pow_succ, map_mul]
    ring
  have hpk : algebraMap A B (ϖ ^ k) ≠ 0 := by
    rw [← map_zero (algebraMap A B)]
    exact fun h => pow_ne_zero k hϖ.ne_zero (hinj h)
  have e2 := mul_left_cancel₀ hpk e
  have hunit : IsUnit (algebraMap A B ϖ) :=
    isUnit_of_mul_isUnit_left (e2 ▸ (u.isUnit.map (algebraMap A B)))
  exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap A B) ϖ).mp hunit)

private theorem key (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [CommRing B] [IsDomain B] [ValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] [Algebra.IsAlgebraic A B]
    (n : ℕ) (h : Module.rank A B ≤ n) (hf : Finite (ResidueField A)) :
    ∃ _ : IsDiscreteValuationRing B, IsAdicComplete (maximalIdeal B) B ∧ Finite (ResidueField B) := by
  haveI : IsHausdorff (maximalIdeal A) B := haus A B
  haveI : Module.Finite A (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) := fin_quot A B n h
  haveI : Module.Finite A B := GlobalTheory.finite_of_isHausdorff_of_finite_quotient (maximalIdeal A) B
  haveI : IsNoetherianRing B := isNoetherian_of_tower A inferInstance
  have hnf : ¬ IsField B := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    intro hF
    have h0 : algebraMap A B ϖ ≠ 0 := by
      rw [← map_zero (algebraMap A B)]
      exact fun e => hϖ.ne_zero (FaithfulSMul.algebraMap_injective A B e)
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel h0
    have hu : IsUnit (algebraMap A B ϖ) := ⟨⟨_, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap A B) ϖ).mp hu)
  haveI hd : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 1 0).mp (inferInstance : ValuationRing B)
  exact ⟨hd, GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite A B,
    IsLocalRing.ResidueField.finite_of_finite hf⟩

theorem UpperTheory.V.Ws.smallExt :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V), 𝔞.IsDvr f →
      ∀ s : Finset 𝔞.K, ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (f' : A' →+* 𝔞.V) (g : A →+* A'),
        𝔞.IsDvr f' ∧ f'.comp g = f ∧ ∀ x : 𝔞.V, (x : 𝔞.K) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ s) → x ∈ f'.range := by
  intro l _ 𝔞 A _ _ _ f hf s
  classical
  have hinjK : Function.Injective (𝔞.toK.comp f) := fun a b h => hf.inj (Subtype.val_injective h)
  let E := FractionRing A
  let φ : E →+* 𝔞.K := IsFractionRing.lift hinjK
  letI : Algebra E 𝔞.K := φ.toAlgebra
  letI : Algebra A 𝔞.K := (𝔞.toK.comp f).toAlgebra
  haveI : IsScalarTower A E 𝔞.K :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsFractionRing.lift_algebraMap hinjK a).symm)
  have hint : ∀ x ∈ (s : Set 𝔞.K), IsIntegral E x := by
    intro x _
    obtain ⟨p, hp0, hp⟩ := hf.alg x
    refine IsAlgebraic.isIntegral ⟨p.map (algebraMap A E), ?_, ?_⟩
    · exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective A E)).mpr hp0
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
      exact hp
  let L' : IntermediateField E 𝔞.K := IntermediateField.adjoin E (s : Set 𝔞.K)
  haveI : FiniteDimensional E L' := IntermediateField.finiteDimensional_adjoin hint
  have hcl : ∀ y ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ ↑s), y ∈ L' := by
    intro y hy
    have hle : Subfield.closure (Set.range (𝔞.toK.comp f) ∪ ↑s) ≤ L'.toSubfield := by
      rw [Subfield.closure_le]
      rintro z (⟨a, rfl⟩ | hz)
      · show (𝔞.toK.comp f) a ∈ L'
        have e : (𝔞.toK.comp f) a = algebraMap E 𝔞.K (algebraMap A E a) :=
          (IsFractionRing.lift_algebraMap hinjK a).symm
        rw [e]
        exact L'.algebraMap_mem _
      · exact IntermediateField.subset_adjoin E _ hz
    exact hle hy
  let B : Subring 𝔞.V := Subring.comap 𝔞.toK L'.toSubfield.toSubring
  have hBext : ∀ x y : B, ((x : 𝔞.V) : 𝔞.K) = ((y : 𝔞.V) : 𝔞.K) → x = y :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have hBmem : ∀ x : B, ((x : 𝔞.V) : 𝔞.K) ∈ L' := fun x => x.2
  let g : A →+* B := f.codRestrict B (fun a => by
    have := hcl ((𝔞.toK.comp f) a) (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
    exact this)
  have hgi : Function.Injective g := fun a b h => hf.inj (congrArg Subtype.val h)
  letI : Algebra A B := g.toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hgi
  haveI : IsLocalHom (algebraMap A B) := ⟨fun a ha => by
    haveI := hf.loc
    exact (isUnit_map_iff f a).mp (ha.map B.subtype)⟩
  have hdvd : ∀ a b : B, a ∣ b ∨ b ∣ a := by
    intro a b
    by_cases ha : ((a : 𝔞.V) : 𝔞.K) = 0
    · right
      exact ⟨0, hBext _ _ (by simp [ha])⟩
    by_cases hb : ((b : 𝔞.V) : 𝔞.K) = 0
    · left
      exact ⟨0, hBext _ _ (by simp [hb])⟩
    have hq : ((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K) ∈ L' := L'.div_mem (hBmem b) (hBmem a)
    rcases 𝔞.V.mem_or_inv_mem (((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K)) with hv | hv
    · left
      refine ⟨⟨⟨_, hv⟩, hq⟩, hBext _ _ ?_⟩
      show ((b : 𝔞.V) : 𝔞.K) = ((a : 𝔞.V) : 𝔞.K) * (((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K))
      field_simp
    · right
      refine ⟨⟨⟨_, hv⟩, L'.inv_mem hq⟩, hBext _ _ ?_⟩
      show ((a : 𝔞.V) : 𝔞.K) = ((b : 𝔞.V) : 𝔞.K) * (((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K))⁻¹
      field_simp
  haveI : ValuationRing B := ValuationRing.iff_dvd_total.mpr ⟨hdvd⟩
  haveI : Algebra.IsAlgebraic A B := ⟨fun x => by
    obtain ⟨p, hp0, hp⟩ := hf.alg ((x : 𝔞.V) : 𝔞.K)
    refine ⟨p, hp0, ?_⟩
    have e : (𝔞.toK.comp B.subtype) (Polynomial.aeval x p) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
      exact hp
    exact hBext _ _ e⟩
  haveI : IsAdicComplete (maximalIdeal A) A := hf.complete
  let ψ : B →ₗ[A] L' :=
    { toFun := fun x => ⟨((x : 𝔞.V) : 𝔞.K), hBmem x⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hψ : Function.Injective ψ := fun x y h => hBext x y (by
    have h' := congrArg (fun z : L' => (z : 𝔞.K)) h
    exact h')
  have hrank : Module.rank A B ≤ (Module.finrank E L' : ℕ) := by
    calc Module.rank A B ≤ Module.rank A L' := LinearMap.rank_le_of_injective ψ hψ
      _ = Module.rank E L' := (IsFractionRing.rank_right_eq A E L').symm
      _ = Module.finrank E L' := (Module.finrank_eq_rank E L').symm
  obtain ⟨hd, hc, hfin⟩ := key A B (Module.finrank E L') hrank hf.fin
  refine ⟨B, inferInstance, inferInstance, hd, B.subtype, g, ?_, RingHom.ext fun a => rfl, ?_⟩
  · refine ⟨Subtype.val_injective, ⟨fun x hx => ?_⟩, hc, hfin, fun x => ?_⟩
    · obtain ⟨u, hu⟩ := hx
      have hu' : (u : 𝔞.V) = x := hu
      have hxy : ((x : 𝔞.V) : 𝔞.K) * (((u⁻¹ : 𝔞.Vˣ) : 𝔞.V) : 𝔞.K) = 1 := by
        rw [← hu']
        exact congrArg Subtype.val u.mul_inv
      have hmem : (((u⁻¹ : 𝔞.Vˣ) : 𝔞.V) : 𝔞.K) ∈ L' := by
        rw [eq_inv_of_mul_eq_one_right hxy]
        exact L'.inv_mem (hBmem x)
      exact ⟨⟨x, ⟨_, hmem⟩, hBext _ _ hxy, hBext _ _ (by rw [mul_comm]; exact hxy)⟩, rfl⟩
    · obtain ⟨p, hp0, hp⟩ := hf.alg x
      refine ⟨p.map g, (Polynomial.map_ne_zero_iff hgi).mpr hp0, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hp
  · intro x hx
    exact RingHom.mem_range.mpr ⟨⟨x, hcl _ hx⟩, rfl⟩
end

