import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk015

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361607021960278843, 361607021970167934⟩, ⟨(-1662492454543915623), (-1662492444432660101)⟩, true⟩

def state01 : KState := ⟨⟨360542769238338028, 360542769248367806⟩, ⟨(-62819997454956051), (-62819987131947517)⟩, true⟩

def words00 : List Nat := [360500291218245865, 360500724698617212, 360500919659858489, 360501114362016568, 360501114362029305, 360501058060838573, 360501168757907339, 360501279308263124, 360501279308276503, 360501194141066716]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360667222463735917, 360667222473908223⟩, ⟨(-250593383642954677), (-250593373104020449)⟩, true⟩

def words01 : List Nat := [360501648134632676, 360502101528079619, 360502636186671753, 360502752973648375, 360502752973662256, 360502480855668338, 360502209096429715, 360502249878024883, 360502358412639931, 360502466804543319]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360423948555079825, 360423948565396500⟩, ⟨115415459242717594, 115415470001810264⟩, true⟩

def words02 : List Nat := [360502466804556983, 360502303540275255, 360501725812447340, 360501568497484552, 360501411388832612, 360501096764398710, 360500824035598477, 360500334023772229, 360499844652900494, 360499383513110102]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨359499964727421481, 359499964737882217⟩, ⟨1538227071930377311, 1538227082910623797⟩, true⟩

def words03 : List Nat := [360499699950135068, 360500065181731493, 360500097410728793, 360500097410744122, 360500096691948758, 360499972203545436, 360499857824470372, 360499857824485690, 360499462517535081, 360498813493018986]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨359915246724419462, 359915246735025437⟩, ⟨897278459615586504, 897278470820237936⟩, true⟩

def words04 : List Nat := [360498165310841247, 360497630937468464, 360497414950937847, 360497510988124424, 360497510988138585, 360497240286219363, 360496568599402402, 360495621188079496, 360494675000007527, 360494136071038494]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360600689283756259, 360600689294510193⟩, ⟨(-170405372634976229), (-170405361200244747)⟩, true⟩

def words05 : List Nat := [360493762834858967, 360493060270945025, 360492358611811113, 360492120943245065, 360492120943258127, 360492058052811948, 360491995243148349, 360491717205095641, 360491455088594897, 360491525065682362]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360916293928074356, 360916293938975834⟩, ⟨(-666577160104508164), (-666577148438854362)⟩, true⟩

def words06 : List Nat := [360491549844522320, 360491582088565500, 360491582088579431, 360491402689068412, 360491223518819413, 360490927924543380, 360491231618056252, 360491581537649740, 360491722506832977, 360491992762375673]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361278207336524112, 361278207347573871⟩, ⟨(-1238940872663454340), (-1238940860764245538)⟩, true⟩

def words07 : List Nat := [360492657765108611, 360493321922324411, 360493864743027867, 360494020725333144, 360494020725347962, 360493795469129065, 360493570498584161, 360493570956940468, 360494067562263787, 360494563539373843]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361328085622440841, 361328085633641568⟩, ⟨(-1320012394021154755), (-1320012381882655261)⟩, true⟩

def words08 : List Nat := [360494771029883791, 360495013172719782, 360495645018439022, 360496276066881326, 360496793840879308, 360497266085858418, 360497487491955032, 360497708619379868, 360497889167030725, 360498410975010107]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360145376028496016, 360145376039847080⟩, ⟨566613660030356979, 566613672408653271⟩, true⟩

def words09 : List Nat := [360499050065560094, 360499688353739510, 360500090885399441, 360500117297114639, 360500117297128108, 360499841233910239, 360499672895424099, 360499731056957296, 360499731056971622, 360499509585102489]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk015
