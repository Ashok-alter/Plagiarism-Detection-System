# Plagiarism Detection System

A web-based document similarity analyzer built for DAA/WT practical work. It lets users upload text, PDF, or DOCX files, compare them using multiple algorithmic approaches, and view similarity scores with a polished report interface.

## Features

- Upload and compare two documents
- Support for .txt, .pdf, and .docx files
- Similarity analysis using multiple algorithms:
  - Dynamic Programming
  - Divide and Conquer
  - Greedy Method
  - Backtracking
  - Branch and Bound
- Visual verdicts, metrics, and score breakdowns
- Report export support and history tracking

## Tech Stack

- Frontend: HTML, CSS, JavaScript
- Backend: Node.js, Express.js
- File parsing: pdf-parse, mammoth
- Real-time support: Socket.IO

## Installation

1. Clone the repository
   ```bash
   git clone https://github.com/Ashok-alter/Plagiarism-Detection-System.git
   ```
2. Navigate to the project folder
   ```bash
   cd Plagiarism-Detection-System
   ```
3. Install dependencies
   ```bash
   npm install
   ```
4. Start the server
   ```bash
   npm start
   ```
5. Open the app in your browser at:
   ```text
   http://localhost:3000
   ```

## Project Structure

- index.html - Main UI
- styles.css - Styling
- script.js - Frontend logic and analysis
- server.js - Backend server and document parsing
- package.json - Project dependencies and scripts

## Notes

This project is intended for academic demonstration and practical understanding of document similarity and algorithmic comparison techniques.
