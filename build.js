/* 
 * LLM is so helpful in writing frontend!
 */

const fs = require('fs');
const path = require('path');
const yaml = require('js-yaml');
const Handlebars = require('handlebars');
const fm = require('front-matter'); // To parse YAML frontmatter in MD files
const { marked } = require('marked');

// --- CONFIGURATION ---
const AGDA_OUT_DIR = './tmp'; // Where Agda output the .md files
const OUTPUT_DIR = './docs';  // Where we want the final site
const STATIC_DIR = './static';
const TEMPLATE_PATH = './templates/layout.hbs';
const INDEX_PATH = './contents/index.md';
const CATALOG_PATH = './contents/catalog.yml';

// Ensure output dir exists
if (!fs.existsSync(OUTPUT_DIR)) fs.mkdirSync(OUTPUT_DIR, { recursive: true });

// 1. READ CATALOG AND TEMPLATE
const rawCatalog = yaml.load(fs.readFileSync(CATALOG_PATH, 'utf8'));
const templateSource = fs.readFileSync(TEMPLATE_PATH, 'utf8');
const template = Handlebars.compile(templateSource);

// 2. SCAN FILES TO MAP TITLES TO FILENAMES
// We need a map: { "Introduction to Type Theory": "Intro.md" }
const titleToFilename = {};
const files = fs.readdirSync(AGDA_OUT_DIR).filter(f => f.endsWith('.md'));

// We store file data in memory to avoid reading headers twice
const fileDataCache = [];

console.log(`Scanning ${files.length} files...`);

files.forEach(filename => {
    const content = fs.readFileSync(path.join(AGDA_OUT_DIR, filename), 'utf8');
    const parsed = fm(content);

    // We assume the frontmatter has a 'title' field
    const title = parsed.attributes.title || filename;

    titleToFilename[title] = filename;

    fileDataCache.push({
        filename,
        title,
        attributes: parsed.attributes,
        body: parsed.body
    });
});

// handle index page
const index_parsed = fm(fs.readFileSync(INDEX_PATH, 'utf8'));
const index_title = index_parsed.attributes.title;

titleToFilename[index_title] = 'index.html';

fileDataCache.push({
    filename: 'index.html',
    title: index_title,
    attributes: index_parsed.attributes,
    body: index_parsed.body
});

// 3. GENERATE HTML FILES
fileDataCache.forEach(file => {
    // A. Prepare the Sidebar Data for THIS specific page
    // We need to mark which page is 'active' and resolve filenames
    const sidebarData = rawCatalog.catalog.map(section => ({
        section: section.section,
        pages: section.pages.map(pageTitle => {
            const targetFilename = titleToFilename[pageTitle];
            // Agda links point to .html, so we swap extension
            const targetUrl = targetFilename ? targetFilename.replace('.md', '.html') : '#';

            return {
                title: pageTitle,
                url: targetUrl,
                isActive: pageTitle === file.title
            };
        })
    }));

    // B. Convert Markdown content to HTML
    const htmlContent = marked.parse(file.body);

    // C. Apply Handlebars Template
    const fullHtml = template({
        title: file.title,
        sidebar: sidebarData,
        content: htmlContent,
        ...file.attributes // pass other metadata to template if needed
    });

    // D. Write to disk
    const outFilename = file.filename.replace('.md', '.html');
    fs.writeFileSync(path.join(OUTPUT_DIR, outFilename), fullHtml);
    console.log(`Generated: ${outFilename}`);
});

// Copy the remaining htmls
fs.readdirSync(AGDA_OUT_DIR).filter(f => f.endsWith('.html')).forEach(file => {
    fs.copyFileSync(path.join(AGDA_OUT_DIR, file), path.join(OUTPUT_DIR, file));
})

// Copy statics
fs.cpSync(STATIC_DIR, path.join(OUTPUT_DIR, 'static'), { recursive: true });

console.log("Build complete.");