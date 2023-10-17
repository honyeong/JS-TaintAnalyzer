const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

// 실행할 스크립트 파일이 있는 폴더 경로
const baseScriptPath = '../CustomTRC/results/';
const projectPath = './build/bin/hermes'

// 스크립트 파일을 동기적으로 실행하는 함수
function executeScriptFile(filePath) {
  try {
    const result = execSync(`${projectPath} -O -dump-ir ${filePath}`, { encoding: 'utf-8' });
    console.log(`Script Output (${filePath}):`);
    console.log(result);
  } catch (error) {
    console.error(`Error executing script (${filePath}):`);
    console.error(error.stderr || error.message);
  }
}

// 주어진 폴더와 하위 폴더에서 스크립트 파일 찾기
function findAndExecuteScripts(folderPath) {
  const files = fs.readdirSync(folderPath);
  for (const file of files) {
    const filePath = path.join(folderPath, file);
    const stat = fs.statSync(filePath);

    if (stat.isDirectory()) {
      // 하위 폴더에 대한 재귀 호출
      findAndExecuteScripts(filePath);
    } else if (stat.isFile() && path.extname(file) === '.js') {
      // 확장자가 .js인 스크립트 파일을 실행
      executeScriptFile(filePath);
    }
  }
}

// 스크립트 실행 시작
findAndExecuteScripts(baseScriptPath);