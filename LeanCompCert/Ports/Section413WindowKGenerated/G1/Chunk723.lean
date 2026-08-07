import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk723

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483769642769661, 362483847415557173⟩, ⟨98547569915348625, 102344984883827487⟩, true⟩

def state01 : KState := ⟨⟨362476928193580731, 362477005988503508⟩, ⟨593194678196351539, 596993693660138129⟩, true⟩

def words00 : List Nat := [371285263059952388, 371285263062433738, 371285262911820086, 371285262701583524, 371285262490369721, 371285262338143628, 371285262114828462, 371285262083568558, 371285262051494186, 371285262020776502]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501517592255571, 362501595409627192⟩, ⟨(-1184952748221487233), (-1181152109370476583)⟩, true⟩

def words01 : List Nat := [371285261966029185, 371285262026767083, 371285262277214026, 371285262403360575, 371285262500187954, 371285262597745187, 371285262774622365, 371285262876876111, 371285263104404682, 371285263333060628]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490655949823683, 362490733789571052⟩, ⟨(-399437398795957989), (-395635141617214563)⟩, true⟩

def words02 : List Nat := [371285263561384738, 371285263563866868, 371285263668341586, 371285263802376322, 371285263938530280, 371285263941015634, 371285263893460353, 371285263847433107, 371285263924419598, 371285264002873548]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479465580640021, 362479543442755054⟩, ⟨410028047998040375, 413831923142116151⟩, true⟩

def words03 : List Nat := [371285264160521540, 371285264319136315, 371285264465199357, 371285264467682267, 371285264384148239, 371285264275890422, 371285264245876493, 371285264248402352, 371285264170482686, 371285264094167027]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490437317672066, 362490515201979203⟩, ⟨(-383666325668640611), (-379860845031862361)⟩, true⟩

def words04 : List Nat := [371285264128536572, 371285264148186184, 371285264337308045, 371285264527456864, 371285264686884083, 371285264689367491, 371285264649194029, 371285264680660165, 371285264876737847, 371285264951878557]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499217198900795, 362499295105930560⟩, ⟨(-1018916552790162508), (-1015109428064511316)⟩, true⟩

def words05 : List Nat := [371285265025340336, 371285265099717069, 371285265363759524, 371285265545544023, 371285265762809881, 371285265980996765, 371285266191994075, 371285266308149357, 371285266503738351, 371285266700739028]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492832898186648, 362492910827319629⟩, ⟨(-556876621910145413), (-553067897678953679)⟩, true⟩

def words06 : List Nat := [371285267077863062, 371285267221815238, 371285267365822904, 371285267510642854, 371285267680589272, 371285267783543408, 371285268076103150, 371285268369697989, 371285268598720211, 371285268706889085]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362504211060953659, 362504289012539283⟩, ⟨(-1380413772106254362), (-1376603422865271284)⟩, true⟩

def words07 : List Nat := [371285268905315708, 371285269104987115, 371285269378184697, 371285269397829826, 371285269399754433, 371285269395423311, 371285269557030477, 371285269631917549, 371285269896373602, 371285270161972626]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495708818338934, 362495786792324842⟩, ⟨(-765031807143278918), (-761219836459578884)⟩, true⟩

def words08 : List Nat := [371285270412061714, 371285270414545904, 371285270594788795, 371285270782406129, 371285271020371404, 371285271063134482, 371285271066734397, 371285271071098593, 371285271250923343, 371285271399023747]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487209656154335, 362487287652525241⟩, ⟨(-149691439984655291), (-145877848734773045)⟩, true⟩

def words09 : List Nat := [371285271644775702, 371285271891542690, 371285272120919035, 371285272191850047, 371285272319813351, 371285272449002358, 371285272702940810, 371285272732595373, 371285272762283333, 371285272792941330]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk723
