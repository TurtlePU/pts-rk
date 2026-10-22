import Foundation
import AppKit
import PDFKit

// Render every page and verify that the new mathematical boundaries survive
// Markdown--TeX/PDF generation. Visual inspection is recorded separately.
let input = CommandLine.arguments[1]
let output = CommandLine.arguments[2]
let kind = CommandLine.arguments[3]
guard let document = PDFDocument(url: URL(fileURLWithPath: input)) else {
    fatalError("Unreadable PDF")
}
let pages = (0..<document.pageCount).map { document.page(at: $0)! }
for (index, page) in pages.enumerated() {
    guard let content = page.string,
          !content.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty else {
        fatalError("Empty text on page \(index + 1)")
    }
}
let text = pages.map { $0.string ?? "" }.joined(separator: "\n")
let flat = text.replacingOccurrences(of: "-\n", with: "")
    .replacingOccurrences(of: "\n", with: " ")
let needles = kind == "interpreter"
    ? ["Algebra", "GenericFold", "UnifiedAlgebra", "PHOASFold", "PHOASCPS", "CombinatoryFold",
       "Brown", "dependent", "numeral", "signature", "soundness"]
    : ["UnifiedAlgebra", "Algebra", "combinatory", "soundness", "Pakhomov"]
for needle in needles {
    guard flat.contains(needle) else { fatalError("Missing text: \(needle)") }
}
let links = pages.flatMap { $0.annotations.compactMap { $0.url?.absoluteString } }
if kind == "interpreter" {
    guard links.contains("https://doi.org/10.1145/2837614.2837623") else {
        fatalError("Missing Brown--Palsberg primary citation")
    }
}
try text.write(toFile: output + "/text.txt", atomically: true, encoding: .utf8)
for (index, page) in pages.enumerated() {
    let bounds = page.bounds(for: .mediaBox)
    let img = page.thumbnail(of: NSSize(width: bounds.width * 1.4,
                                      height: bounds.height * 1.4), for: .mediaBox)
    guard let data = img.tiffRepresentation,
          let bitmap = NSBitmapImageRep(data: data),
          let png = bitmap.representation(using: .png, properties: [:]) else {
        fatalError("Cannot render page \(index + 1)")
    }
    try png.write(to: URL(fileURLWithPath: output + "/page-\(index + 1).png"))
}
print("PASS: \(document.pageCount) pages, \(links.count) links, required text and all-page rendering")
