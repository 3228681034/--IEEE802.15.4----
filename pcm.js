const fs = require('fs');
const path = require('path');

// 引入 Opus 编解码器库
const { OpusEncoder, OpusDecoder } = require('opus-recorder');

// 初始化 Opus 编解码器
const encoder = new OpusEncoder({
    sampleRate: 48000, // 采样率
    channels: 1,      // 单声道
    application: 'voip' // 应用场景
});

const decoder = new OpusDecoder({
    sampleRate: 48000,
    channels: 1
});

// 读取本地 PCM 文件
function loadPCMFile(filePath) {
    const buffer = fs.readFileSync(filePath);
    const audioData = new Int16Array(buffer.buffer, buffer.byteOffset, buffer.byteLength / 2);
    return audioData;
}

// 编码语音数据
function encodeAudioData(audioData) {
    const encodedData = encoder.encode(audioData);
    const encodedBuffer = new Uint8Array(encodedData);
    return encodedBuffer;
}

// 解码语音数据
function decodeAudioData(encodedData) {
    const decodedData = decoder.decode(encodedData);
    const decodedAudioData = new Int16Array(decodedData);
    return decodedAudioData;
}

// 保存编码后的数据到文件
function saveEncodedData(encodedData, outputFilePath) {
    fs.writeFileSync(outputFilePath, encodedData);
    console.log(`编码后的数据已保存到: ${outputFilePath}`);
}

// 主程序
(async () => {
    try {
        // 加载本地 PCM 文件
        const inputFilePath = 'C:\\Users\\Administrator\\Desktop\\学习\\本科毕业\\音频\\one.wav';
        const audioData = loadPCMFile(inputFilePath);
        console.log('加载的音频数据:', audioData);

        // 编码语音数据
        const encodedBuffer = encodeAudioData(audioData);
        console.log('编码后的数据:', encodedBuffer);

        // 解码语音数据
        const decodedAudioData = decodeAudioData(encodedBuffer);
        console.log('解码后的音频数据:', decodedAudioData);

        // 保存编码后的数据到文件
        const outputFilePath = 'C:\\Users\\Administrator\\Desktop\\学习\\本科毕业\\音频\\encoded.opus';
        saveEncodedData(encodedBuffer, outputFilePath);
    } catch (error) {
        console.error('发生错误:', error);
    }
})();