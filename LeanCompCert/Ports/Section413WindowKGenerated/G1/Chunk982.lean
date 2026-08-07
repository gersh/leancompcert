import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk982

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474682142208531, 362474829047380888⟩, ⟨1024396267066656669, 1034136008332351029⟩, true⟩

def state01 : KState := ⟨⟨362481239396466721, 362481386332576462⟩, ⟨380462090436298188, 390204869903314898⟩, true⟩

def words00 : List Nat := [371285359859062307, 371285359851259677, 371285359802980846, 371285359798914126, 371285359793804097, 371285359773381715, 371285359613643023, 371285359559554160, 371285359503561899, 371285359500990100]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477665198726628, 362477812166167576⟩, ⟨731537079719841628, 741282936390486382⟩, true⟩

def words01 : List Nat := [371285359463117838, 371285359423850287, 371285359443957545, 371285359456777520, 371285359488107943, 371285359520779320, 371285359531772708, 371285359535222128, 371285359407743863, 371285359335139176]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481852460617409, 362481999458811218⟩, ⟨320240075102782200, 329988952476028142⟩, true⟩

def words02 : List Nat := [371285359287515264, 371285359290965404, 371285359197110311, 371285359098708376, 371285358998877307, 371285358932536220, 371285358824178920, 371285358820921212, 371285358816511149, 371285358808831335]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491250520231513, 362491397549646549⟩, ⟨(-603005556560284465), (-593253612167334819)⟩, true⟩

def words03 : List Nat := [371285358785661487, 371285358798470357, 371285358884014888, 371285358887465014, 371285358835227255, 371285358753483125, 371285358683372194, 371285358687241082, 371285358726376350, 371285358791773896]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473654800970499, 362473801861477543⟩, ⟨1125642208109269172, 1135397207142903440⟩, true⟩

def words04 : List Nat := [371285358833684754, 371285358837135233, 371285358740673989, 371285358711232328, 371285358680125510, 371285358653123403, 371285358487154088, 371285358322184603, 371285358155787284, 371285358067148209]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472615139999372, 362472762231603156⟩, ⟨1227845789436051369, 1237603843879679951⟩, true⟩

def words05 : List Nat := [371285357951868363, 371285357941698830, 371285357930327393, 371285357919184229, 371285357807907249, 371285357723676454, 371285357652824435, 371285357656275646, 371285357550760213, 371285357426431975]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483215781846115, 362483362904311864⟩, ⟨186183325200296860, 195944412299237696⟩, true⟩

def words06 : List Nat := [371285357300590706, 371285357262565013, 371285357177560720, 371285357146951049, 371285357115235378, 371285357068378821, 371285356934265064, 371285356870263620, 371285356840008510, 371285356843584269]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476732662846225, 362476879816897967⟩, ⟨823324708255785877, 833088899453134955⟩, true⟩

def words07 : List Nat := [371285356825898025, 371285356802756616, 371285356783241243, 371285356787070908, 371285356757952249, 371285356761931962, 371285356764520318, 371285356745181270, 371285356586727617, 371285356504926591]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362462222458134541, 362462369642874811⟩, ⟨2249486027842679775, 2259253235273020629⟩, true⟩

def words08 : List Nat := [371285356421019305, 371285356414785816, 371285356279120936, 371285356145032135, 371285356009670770, 371285355881022258, 371285355699302164, 371285355546829274, 371285355393172233, 371285355228745938]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486194815926858, 362486342031824914⟩, ⟨(-106884529257421771), (-97114259169947125)⟩, true⟩

def words09 : List Nat := [371285354997233939, 371285354859453148, 371285354719932579, 371285354649936763, 371285354515911974, 371285354367080478, 371285354216789442, 371285354171551326, 371285354090444412, 371285354104345337]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk982
