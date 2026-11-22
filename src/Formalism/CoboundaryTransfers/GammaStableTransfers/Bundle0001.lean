import Formalism.CoboundaryTransfers.StatementAPI

-- bundled from Formalism.CoboundaryTransfers.GammaStableTransfers.DiffOneSmulOfTower
section
noncomputable section

namespace Formalism.CoboundaryTransfers

section DiagramChase₂
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']

lemma chase_qpow_bij (W : WachMod B M D) (j : ℕ) :
    Function.Bijective (fun x : D => B.Q ^ j • x) := by
  induction j with
  | zero =>
    simp only [pow_zero, one_smul]
    exact Function.bijective_id
  | succ n ih =>
    have h : (fun x : D => B.Q ^ (n + 1) • x) = (fun x : D => B.Q ^ n • x) ∘ (fun x : D => B.Q • x) := by
      funext x
      simp only [Function.comp, pow_succ, mul_smul]
    rw [h]
    exact ih.comp W.Q_bij

lemma chase_Q_sub (W : WachMod B M D) {x y : D} (hx : W.QInv x) (hy : W.QInv y) :
    W.QInv (x - y) := by
  show B.Q ^ M • (x - y) ∈ W.N
  rw [smul_sub]
  exact W.N.sub_mem hx hy
lemma chase_Q_smul (W : WachMod B M D) (r : O) {x : D} (hx : W.QInv x) : W.QInv (r • x) := by
  show B.Q ^ M • (r • x) ∈ W.N
  rw [algebra_compatible_smul A r x, smul_comm (B.Q ^ M) (algebraMap O A r) x]
  exact W.N.smul_mem _ hx
lemma chase_Q_smulA (W : WachMod B M D) (b : A) {x : D} (hx : W.QInv x) : W.QInv (b • x) := by
  show B.Q ^ M • (b • x) ∈ W.N
  rw [smul_comm (B.Q ^ M) b x]
  exact W.N.smul_mem b hx
lemma chase_Q_N (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv x := by
  show B.Q ^ M • x ∈ W.N
  exact W.N.smul_mem _ hx
lemma chase_Q_φ (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv (W.φ x) := by
  show B.Q ^ M • W.φ x ∈ W.N
  exact W.φ_N x hx

lemma WachMod_d1_smul (W : WachMod B M D) (r : O) (y z : D) :
    W.d1 (r • y) (r • z) = r • W.d1 y z := by
  simp only [WachMod.d1, map_smul, smul_sub]
lemma diffOne_sub (W : WachMod B M D) (y z y' z' : D) :
    W.d1 (y - y') (z - z') = W.d1 y z - W.d1 y' z' := by
  simp only [WachMod.d1, map_sub]
  abel
lemma WachMod_d1_phi_sub_gamma_sub_eq_zero (W : WachMod B M D) (x : D) : W.d1 (W.φ x - x) (W.γ x - x) = 0 := by
  have hc : ∀ y : D, W.φ (W.γ y) = W.γ (W.φ y) := by
    cases W
    assumption
  simp only [WachMod.d1, map_sub, hc]
  abel
lemma map_diffOne {W : WachMod B M D} {W' : WachMod B M D'} (f : Hom W W') (y z : D) :
    f.f (W.d1 y z) = W'.d1 (f.f y) (f.f z) := by
  have hφ : ∀ x, f.f (W.φ x) = W'.φ (f.f x) := by
    cases f
    first | assumption | done
  have hγ : ∀ x, f.f (W.γ x) = W'.γ (f.f x) := by
    cases f
    first | assumption | done
  simp only [WachMod.d1, map_sub, hφ, hγ]
lemma chase_hom_Q {W : WachMod B M D} {W' : WachMod B M D'} (f : Hom W W') {y : D}
    (hy : W.QInv y) : W'.QInv (f.f y) := by
  have hN : ∀ x ∈ W.N, f.f x ∈ W'.N := by
    cases f
    first | assumption | done
  show B.Q ^ M • f.f y ∈ W'.N
  rw [← map_smul f.f]
  exact hN _ hy

end DiagramChase₂

private lemma exists_phi_X_eq_X_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) :
    ∃ v, B.φ B.X = B.X * v := by
  cases B
  assumption

theorem cocycleLiftOfExact_holds : DiagramChase₂ := by
  unfold DiagramChase₂
  intro O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e c hC hR hT
  unfold CokerKilled at hC
  unfold RatSurj at hR
  unfold WachMod.TorsKilled at hT
  unfold Lifts

  have hpφ : ∀ t, S.π.f (W₁.φ t) = W₂.φ (S.π.f t) := by
    generalize S.π = g
    cases g
    assumption
  have hpγ : ∀ t, S.π.f (W₁.γ t) = W₂.γ (S.π.f t) := by
    generalize S.π = g
    cases g
    assumption
  have hiN : ∀ t ∈ W₀.N, S.ι.f t ∈ W₁.N := by
    generalize S.ι = g
    cases g
    assumption
  have hpO : ∀ (r : O) (t : D₁), S.π.f (r • t) = r • S.π.f t := by
    intro r t
    first
    | exact LinearMap.map_smul_of_tower _ r t
    | rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]
  have hiO : ∀ (r : O) (t : D₀), S.ι.f (r • t) = r • S.ι.f t := by
    intro r t
    first
    | exact LinearMap.map_smul_of_tower _ r t
    | rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]

  have key : ∀ (w : D₀) (t : D₁), S.ι.f w = B.X • t → ∃ t₀, S.ι.f t₀ = t ∧ w = B.X • t₀ := by
    intro w t h
    have h0 : S.π.f t = 0 := by
      apply W₂.X_inj
      rw [← map_smul, ← h]
      exact (S.exact _).2 ⟨w, rfl⟩
    obtain ⟨t₀, ht₀⟩ := (S.exact t).1 h0
    refine ⟨t₀, ht₀, S.ι_inj ?_⟩
    rw [map_smul, ht₀, h]
  have qsat : ∀ w : D₀, W₁.QInv (S.ι.f w) → W₀.QInv w := by
    intro w h
    show B.Q ^ M • w ∈ W₀.N
    apply S.sat
    rw [map_smul]
    exact h
  intro y z hyz
  obtain ⟨k, y₁, z₁, hc₁, x, hx, hpy₁, hpz₁⟩ := hR y z hyz
  obtain ⟨⟨hQy, n, hn, rfl⟩, hd⟩ := hyz
  obtain ⟨⟨hQy₁, n₁, hn₁, hz₁⟩, hd₁⟩ := hc₁

  obtain ⟨a, ha, hpa⟩ := hC (B.Q ^ M • y) hQy
  obtain ⟨yt, hyt⟩ : ∃ t, B.Q ^ M • t = a := (chase_qpow_bij W₁ M).2 a
  have hQyt : W₁.QInv yt := by
    show B.Q ^ M • yt ∈ W₁.N
    rw [hyt]
    exact ha
  have hpyt : S.π.f yt = ((B.p : O) ^ e) • y := by
    apply (chase_qpow_bij W₂ M).1
    show B.Q ^ M • S.π.f yt = B.Q ^ M • (((B.p : O) ^ e) • y)
    rw [← map_smul S.π.f, hyt, hpa, smul_comm (B.Q ^ M) ((B.p : O) ^ e) y]
  obtain ⟨b, hb, hpb⟩ := hC n hn
  have hpzt : S.π.f (B.X • b) = ((B.p : O) ^ e) • (B.X • n) := by
    rw [map_smul, hpb, smul_comm B.X ((B.p : O) ^ e) n]
  have hω₁ : S.π.f (W₁.d1 yt (B.X • b)) = 0 := by
    rw [map_diffOne, hpyt, hpzt, WachMod_d1_smul, hd, smul_zero]
  obtain ⟨ω, hω⟩ := (S.exact _).1 hω₁

  obtain ⟨y', hQy', hγyt⟩ := W₁.γ_QN yt hQyt
  obtain ⟨v, hv⟩ := exists_phi_X_eq_X_mul B
  have hiω : S.ι.f ω = B.X • (y' - (v • W₁.φ b - b)) := by
    rw [hω, WachMod.d1, hγyt, W₁.φ_smul, hv, mul_smul, smul_sub, smul_sub]
  have hsmem : W₁.QInv (y' - (v • W₁.φ b - b)) :=
    chase_Q_sub W₁ hQy' (chase_Q_sub W₁ (chase_Q_smulA W₁ v (chase_Q_φ W₁ hb)) (chase_Q_N W₁ hb))
  obtain ⟨s₀, hs₀, hωs₀⟩ := key ω _ hiω
  have hC2 : W₀.C2 ω := ⟨s₀, qsat s₀ (by rw [hs₀]; exact hsmem), hωs₀⟩

  obtain ⟨m, hm, hpm⟩ := hC x hx
  have hpu : S.π.f (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • y) := by
    rw [map_sub, map_sub, hpO, hpφ, hpy₁, hpm, map_smul W₂.φ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) y]
    abel
  have hpv : S.π.f (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • (B.X • n)) := by
    rw [map_sub, map_sub, hpO, hpγ, hpz₁, hpm, map_smul W₂.γ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) (B.X • n)]
    abel
  have hα0 : S.π.f (((B.p : O) ^ k) • yt - (((B.p : O) ^ e) • y₁ - (W₁.φ m - m))) = 0 := by
    rw [map_sub, hpO, hpyt, hpu, sub_self]
  have hβ0 : S.π.f (((B.p : O) ^ k) • (B.X • b) - (((B.p : O) ^ e) • z₁ - (W₁.γ m - m))) = 0 := by
    rw [map_sub, hpO, hpzt, hpv, sub_self]
  obtain ⟨α, hα⟩ := (S.exact _).1 hα0
  obtain ⟨β, hβ⟩ := (S.exact _).1 hβ0
  have hduv : W₁.d1 (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = 0 := by
    rw [diffOne_sub, WachMod_d1_smul, hd₁, smul_zero, WachMod_d1_phi_sub_gamma_sub_eq_zero, sub_zero]
  have hdαβ : W₀.d1 α β = ((B.p : O) ^ k) • ω := by
    apply S.ι_inj
    rw [map_diffOne, hα, hβ, diffOne_sub, hduv, sub_zero, WachMod_d1_smul, ← hω, hiO]
  have hQu : W₁.QInv (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) :=
    chase_Q_sub W₁ (chase_Q_smul W₁ _ hQy₁) (chase_Q_sub W₁ (chase_Q_φ W₁ hm) (chase_Q_N W₁ hm))
  have hQα : W₀.QInv α := qsat α (by rw [hα]; exact chase_Q_sub W₁ (chase_Q_smul W₁ _ hQyt) hQu)
  obtain ⟨m', hm', hγm⟩ := W₁.γ_N m hm
  have hiβ : S.ι.f β = B.X • (((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m')) := by
    rw [hβ, hz₁, hγm, smul_sub, smul_sub, smul_comm B.X ((B.p : O) ^ k) b, smul_comm B.X ((B.p : O) ^ e) n₁]
  have hKb : ((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m') ∈ W₁.N :=
    W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hb) (W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hn₁) hm')
  obtain ⟨β₀, hβ₀, hββ₀⟩ := key β _ hiβ
  have hcob : W₀.IsCob2 (((B.p : O) ^ k) • ω) :=
    ⟨α, β, ⟨hQα, β₀, S.sat β₀ (by rw [hβ₀]; exact hKb), hββ₀⟩, hdαβ.symm⟩

  obtain ⟨α', β', ⟨hQα', n', hn', hβ'⟩, hcω⟩ := hT ω hC2 ⟨k, hcob⟩
  refine ⟨c • yt - S.ι.f α', c • (B.X • b) - S.ι.f β', ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact chase_Q_sub W₁ (chase_Q_smul W₁ c hQyt) (chase_hom_Q S.ι hQα')
  · refine ⟨c • b - S.ι.f n', W₁.N.sub_mem (W₁.N.smul_of_tower_mem c hb) (hiN n' hn'), ?_⟩
    rw [hβ', map_smul, smul_sub, smul_comm B.X c b]
  · rw [diffOne_sub, WachMod_d1_smul, ← map_diffOne S.ι α' β', ← hcω, ← hω, hiO, sub_self]
  · rw [map_sub, hpO, hpyt, (S.exact _).2 ⟨α', rfl⟩, sub_zero, mul_comm, mul_smul]
  · rw [map_sub, hpO, hpzt, (S.exact _).2 ⟨β', rfl⟩, sub_zero, mul_comm, mul_smul]

end Formalism.CoboundaryTransfers
end
end

-- bundled from Formalism.CoboundaryTransfers.GammaStableTransfers.MemCoboundariesOfIsOneCoboundary
section
noncomputable section

namespace Formalism.CoboundaryTransfers

namespace WachMod

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)

theorem smulO_eq (c : O) (x : D) : c • x = algebraMap O A c • x := by
  rw [algebraMap_smul]

theorem smulO_mem (c : O) {x : D} (hx : x ∈ W.N) : c • x ∈ W.N := by
  rw [smulO_eq (A := A)]; exact W.N.smul_mem _ hx

theorem qInv_of_mem {n : D} (hn : n ∈ W.N) : W.QInv n := W.N.smul_mem _ hn

theorem qInv_zero : W.QInv 0 := by
  simp only [QInv, smul_zero]; exact W.N.zero_mem

theorem qInv_add {y y' : D} (hy : W.QInv y) (hy' : W.QInv y') : W.QInv (y + y') := by
  simp only [QInv, smul_add]; exact W.N.add_mem hy hy'

theorem qInv_sub {y y' : D} (hy : W.QInv y) (hy' : W.QInv y') : W.QInv (y - y') := by
  simp only [QInv, smul_sub]; exact W.N.sub_mem hy hy'

theorem qInv_smul (a : A) {y : D} (hy : W.QInv y) : W.QInv (a • y) := by
  simp only [QInv]; rw [smul_comm]; exact W.N.smul_mem a hy

theorem qInv_smulO (c : O) {y : D} (hy : W.QInv y) : W.QInv (c • y) := by
  rw [smulO_eq (A := A)]; exact W.qInv_smul _ hy

theorem xN_mem {z : D} (hz : W.XN z) : z ∈ W.N := by
  obtain ⟨n, hn, rfl⟩ := hz; exact W.N.smul_mem _ hn

theorem xN_zero : W.XN 0 := ⟨0, W.N.zero_mem, (smul_zero _).symm⟩

theorem xN_add {z z' : D} (hz : W.XN z) (hz' : W.XN z') : W.XN (z + z') := by
  obtain ⟨n, hn, rfl⟩ := hz; obtain ⟨n', hn', rfl⟩ := hz'
  exact ⟨n + n', W.N.add_mem hn hn', (smul_add _ _ _).symm⟩

theorem xN_smul (a : A) {z : D} (hz : W.XN z) : W.XN (a • z) := by
  obtain ⟨n, hn, rfl⟩ := hz
  exact ⟨a • n, W.N.smul_mem a hn, smul_comm _ _ _⟩

theorem xN_smulO (c : O) {z : D} (hz : W.XN z) : W.XN (c • z) := by
  rw [smulO_eq (A := A)]; exact W.xN_smul _ hz

theorem cont_pow_X_pow_eq_zero_of_lt : W.C1 0 0 := ⟨W.qInv_zero, W.xN_zero⟩

theorem isOneCochain_add {y z y' z' : D} (h : W.C1 y z) (h' : W.C1 y' z') : W.C1 (y + y') (z + z') :=
  ⟨W.qInv_add h.1 h'.1, W.xN_add h.2 h'.2⟩

theorem isOneCochain_smul_of_tower (c : O) {y z : D} (h : W.C1 y z) : W.C1 (c • y) (c • z) :=
  ⟨W.qInv_smulO c h.1, W.xN_smulO c h.2⟩

theorem cont_X_pow_pow_eq_zero_of_gt : W.C2 0 := ⟨0, W.qInv_zero, (smul_zero _).symm⟩

theorem isTwoCochain_add {ω ω' : D} (h : W.C2 ω) (h' : W.C2 ω') : W.C2 (ω + ω') := by
  obtain ⟨y, hy, rfl⟩ := h; obtain ⟨y', hy', rfl⟩ := h'
  exact ⟨y + y', W.qInv_add hy hy', (smul_add _ _ _).symm⟩

theorem isTwoCochain_smul (a : A) {ω : D} (h : W.C2 ω) : W.C2 (a • ω) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨a • y, W.qInv_smul a hy, smul_comm _ _ _⟩

theorem d1_apply (y z : D) : W.d1 y z = (W.γ y - y) - (W.φ z - z) := rfl

theorem diffOne_zero : W.d1 0 0 = 0 := by simp [d1]

theorem diffOne_add (y z y' z' : D) : W.d1 (y + y') (z + z') = W.d1 y z + W.d1 y' z' := by
  simp only [d1, map_add]; abel

theorem diffOne_smul_of_tower (c : O) (y z : D) : W.d1 (c • y) (c • z) = c • W.d1 y z := by
  simp only [d1, map_smul, smul_sub]

theorem diffOne_diffZero (x : D) : W.d1 (W.φ x - x) (W.γ x - x) = 0 := by
  simp only [d1, map_sub, W.comm]; abel

theorem isOneCochain_diffZero {x : D} (hx : x ∈ W.N) : W.C1 (W.φ x - x) (W.γ x - x) := by
  refine ⟨?_, ?_⟩
  · simp only [QInv, smul_sub]
    exact W.N.sub_mem (W.φ_N x hx) (W.N.smul_mem _ hx)
  · obtain ⟨x', hx', h⟩ := W.γ_N x hx
    exact ⟨x', hx', h⟩

theorem isTwoCochain_diffOne {y z : D} (h : W.C1 y z) : W.C2 (W.d1 y z) := by
  obtain ⟨hy, n, hn, rfl⟩ := h
  obtain ⟨y', hy', hγ⟩ := W.γ_QN y hy
  obtain ⟨v, hv⟩ := B.φX
  refine ⟨y' - (v • W.φ n - n), ?_, ?_⟩
  · refine W.qInv_sub hy' (W.qInv_sub ?_ (W.qInv_of_mem hn))
    refine W.qInv_smul v ?_
    exact W.φ_N n hn
  · rw [d1, hγ, W.φ_smul, hv, mul_smul, smul_sub, smul_sub]

theorem isOneCocycle_diffZero {x : D} (hx : x ∈ W.N) : W.Cocycle (W.φ x - x) (W.γ x - x) :=
  ⟨W.isOneCochain_diffZero hx, W.diffOne_diffZero x⟩

theorem cocycle_of_isCob1 {y z : D} (h : W.IsCob1 y z) : W.Cocycle y z := by
  obtain ⟨x, hx, rfl, rfl⟩ := h; exact W.isOneCocycle_diffZero hx

theorem cocycle_zero : W.Cocycle 0 0 := ⟨W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero⟩

theorem cocycle_add {y z y' z' : D} (h : W.Cocycle y z) (h' : W.Cocycle y' z') :
    W.Cocycle (y + y') (z + z') :=
  ⟨W.isOneCochain_add h.1 h'.1, by rw [W.diffOne_add, h.2, h'.2, add_zero]⟩

theorem cocycle_smulO (c : O) {y z : D} (h : W.Cocycle y z) : W.Cocycle (c • y) (c • z) :=
  ⟨W.isOneCochain_smul_of_tower c h.1, by rw [W.diffOne_smul_of_tower, h.2, smul_zero]⟩

theorem isCob1_zero : W.IsCob1 0 0 := ⟨0, W.N.zero_mem, by simp, by simp⟩

theorem isCob1_add {y z y' z' : D} (h : W.IsCob1 y z) (h' : W.IsCob1 y' z') :
    W.IsCob1 (y + y') (z + z') := by
  obtain ⟨x, hx, rfl, rfl⟩ := h; obtain ⟨x', hx', rfl, rfl⟩ := h'
  refine ⟨x + x', W.N.add_mem hx hx', ?_, ?_⟩ <;> simp only [map_add] <;> abel

theorem isCob1_smulO (c : O) {y z : D} (h : W.IsCob1 y z) : W.IsCob1 (c • y) (c • z) := by
  obtain ⟨x, hx, rfl, rfl⟩ := h
  exact ⟨c • x, W.smulO_mem c hx, by rw [map_smul, smul_sub], by rw [map_smul, smul_sub]⟩

theorem isCob2_zero : W.IsCob2 0 := ⟨0, 0, W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero.symm⟩

theorem isCob2_add {ω ω' : D} (h : W.IsCob2 ω) (h' : W.IsCob2 ω') : W.IsCob2 (ω + ω') := by
  obtain ⟨y, z, hc, rfl⟩ := h; obtain ⟨y', z', hc', rfl⟩ := h'
  exact ⟨y + y', z + z', W.isOneCochain_add hc hc', (W.diffOne_add _ _ _ _).symm⟩

theorem isCob2_smulO (c : O) {ω : D} (h : W.IsCob2 ω) : W.IsCob2 (c • ω) := by
  obtain ⟨y, z, hc, rfl⟩ := h
  exact ⟨c • y, c • z, W.isOneCochain_smul_of_tower c hc, (W.diffOne_smul_of_tower _ _ _).symm⟩

def qInvSub : Submodule A D where
  carrier := {y | W.QInv y}
  add_mem' := W.qInv_add
  zero_mem' := W.qInv_zero
  smul_mem' := fun a _ hy => W.qInv_smul a hy

def xNSub : Submodule A D where
  carrier := {z | W.XN z}
  add_mem' := W.xN_add
  zero_mem' := W.xN_zero
  smul_mem' := fun a _ hz => W.xN_smul a hz

def twoCochains : Submodule A D where
  carrier := {ω | W.C2 ω}
  add_mem' := W.isTwoCochain_add
  zero_mem' := W.cont_X_pow_pow_eq_zero_of_gt
  smul_mem' := fun a _ h => W.isTwoCochain_smul a h

def cocycleSub : Submodule O (D × D) where
  carrier := {pr | W.Cocycle pr.1 pr.2}
  add_mem' := fun h h' => W.cocycle_add h h'
  zero_mem' := W.cocycle_zero
  smul_mem' := fun c _ h => W.cocycle_smulO c h

def isCob1Sub : Submodule O (D × D) where
  carrier := {pr | W.IsCob1 pr.1 pr.2}
  add_mem' := fun h h' => W.isCob1_add h h'
  zero_mem' := W.isCob1_zero
  smul_mem' := fun c _ h => W.isCob1_smulO c h

def isCob2Sub : Submodule O D where
  carrier := {ω | W.IsCob2 ω}
  add_mem' := W.isCob2_add
  zero_mem' := W.isCob2_zero
  smul_mem' := fun c _ h => W.isCob2_smulO c h

theorem mem_Z1_iff_cocycle (y z : D) : (y, z) ∈ W.Z1 ↔ W.d1 y z = 0 := by
  rw [Z1, LinearMap.mem_ker, LinearMap.coprod_apply]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply, d1]
  rw [← sub_eq_add_neg]

theorem mem_cocycles' (pr : D × D) : pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := W.mem_Z1_iff_cocycle pr.1 pr.2

theorem diffZero_mem_coboundaries (x : D) : (W.φ x - x, W.γ x - x) ∈ W.B1 :=
  ⟨x, by simp [LinearMap.prod_apply]⟩

theorem coboundaries_le_cocycles : W.B1 ≤ W.Z1 := by
  rintro _ ⟨x, rfl⟩
  rw [W.mem_cocycles']
  simpa [LinearMap.prod_apply] using W.diffOne_diffZero x

theorem mem_cocycles_of_isOneCocycle {y z : D} (h : W.Cocycle y z) : (y, z) ∈ W.Z1 :=
  (W.mem_Z1_iff_cocycle y z).2 h.2

theorem finiteCocycles_le_cocycles : W.Zf ≤ W.Z1 :=
  sup_le (Submodule.span_le.2 fun _ h => h.1) W.coboundaries_le_cocycles

theorem cocycle_mem_Zf {y z : D} (h : W.Cocycle y z) : (y, z) ∈ W.Zf := by
  refine Submodule.mem_sup_left (Submodule.subset_span ⟨W.mem_cocycles_of_isOneCocycle h, 0, 0,
    W.B1.zero_mem, ?_⟩)
  simp only [pow_zero, one_smul, add_zero]
  exact ⟨⟨M, h.1.1⟩, h.1.2⟩

theorem mem_coboundaries_of_isOneCoboundary {y z : D} (h : W.IsCob1 y z) : (y, z) ∈ W.B1 := by
  obtain ⟨x, _, rfl, rfl⟩ := h; exact W.diffZero_mem_coboundaries x

end WachMod

theorem differentialsComplex_holds : Complex := by
  intro O A _ _ _ B M D _ _ _ _ W
  exact ⟨fun _ hx => W.isOneCochain_diffZero hx, W.diffOne_diffZero, fun _ _ h => W.isTwoCochain_diffOne h,
    fun _ _ h => W.cocycle_of_isCob1 h⟩

theorem cochainsSubmodules_holds : Submods := by
  intro O A _ _ _ B M D _ _ _ _ W
  exact ⟨⟨W.qInvSub, fun _ => Iff.rfl⟩, ⟨W.xNSub, fun _ => Iff.rfl⟩,
    ⟨W.twoCochains, fun _ => Iff.rfl⟩, ⟨W.cocycleSub, fun _ _ => Iff.rfl⟩,
    ⟨W.isCob1Sub, fun _ _ => Iff.rfl⟩, ⟨W.isCob2Sub, fun _ => Iff.rfl⟩,
    fun _ hn => W.qInv_of_mem hn, fun _ h => W.xN_mem h⟩

theorem cocyclesFinite_holds : CocZf := by
  intro O A _ _ _ B M D _ _ _ _ W
  exact ⟨fun _ _ h => W.cocycle_mem_Zf h, W.coboundaries_le_cocycles, W.finiteCocycles_le_cocycles,
    fun _ _ h => W.mem_coboundaries_of_isOneCoboundary h⟩

end Formalism.CoboundaryTransfers
end
end

