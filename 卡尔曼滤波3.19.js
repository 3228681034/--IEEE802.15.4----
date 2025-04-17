const baseParam={
    bandWidth:250000,
    timeSlot:50,        //50ms
    totleSteps:100      //50ms
}

const SIMU_TICK=20;     //ms
const NO_SEND=3;        //每发1包数据，要停发3个节拍tick
const MAX_SEND_TEMP_STORE=16;     //节点待发数据FIFO最大深度
const MAX_SEND_TEMP_TIMEO=20;    //节点待发数据允许保留的最长时间
const MAX_HOP=16;        //数据包最大跳数
const MAX_JUST_RECVED_PACKS=20;    //最近收到的包队列长度，避免重复转发
const MAX_JUST_RECVED_TIMEO=20;    //最近收到的包允许保留的最长时间

const ENTER_GROUP_NEIGHBOR_HOLDING=100;    //邻居中包含入网申请者的时限，tick数

const TTL_NEIGHBOR=200;  //邻居保存时间，tick数
const T_HANDSHAKE=75;    //邻居刷新时间，tick数。到时，节点必须发1个包，共其他节点识别邻居

const ALL_DATA_PACK_NUM=48;  //每个数据源发出的数据包总数

const ALL_STEPS_THESHOLD=500;  //仿真总步数

const PACK_C_ID=999;    //PackC的特殊ID，用来避免出现大量PackC
const DELAY_FOR_HANDSHAKE=160;  //仅适用于仿真，初始时完成邻居发现

const ENERGY_CONSUMPTION_SEND = 2; // 发送数据时的能量消耗
const ENERGY_CONSUMPTION_RECEIVE = 1; // 接收数据时的能量消耗
const ENERGY_CONSUMPTION_IDLE = 0.1; // 空闲时的能量消耗
const alpha = 1;//信息素重要性（通常取值 1
const beta = 2;//启发式信息重要性（通常取值 2-5）
const rho = 0.2;//信息素挥发率（通常取值 0.1-0.5）
const Q = 10;//信息素强度常数（通常取值 10-100）

// 超帧结构参数
const SUPERFRAME_DURATION = 1000; // 超帧总时长（单位：tick）
const CAP_DURATION = 500; // 竞争接入期时长（单位：tick）
const CFP_DURATION = 300; // 无竞争期时长（单位：tick）
const INACTIVE_PERIOD = 200; // 低功耗模式时长（单位：tick）

const MIN_BACKOFF_TIME = 1; // 最小退避时间
const MAX_BACKOFF_TIME = 100; // 最大退避时间
const BACKOFF_EXPONENTIAL_INCREASE = 2; // 退避时间指数增长因子

let pheromoneMatrix = [];//定义信息素值
let etaMatrix = [];//启发式信息矩阵
var LevColor=[];
var LevBkColor=[];
var Nodes=[];
var simulationRunning = false;
//x:0~112   y:0~62  pwrRad=0~9
class devNode{
    constructor(canvas, sNo, pwrRad, x, y, srcVolumn, nodeNum) {



        this.sNo = sNo;
        this.id = 0;
        this.longName = '64byteName_' + sNo.toString();
        this.volumn = srcVolumn;

        this.energy = this.generateInitialEnergy(); // 随机生成初始能量
        this.energyThreshold = 10; // 能量阈值
        this.initialEnergy = this.energy; // 保存初始能量值

        this.justRecvedPacks = [];
        this.isSrc = false;
        this.nPermittedSend = 0;
        this.srcSendDelay = 0;
        this.waitSendFifo = [];
        this.handshaked = 0;
        this.neighborsRssiTtl = [];
        for (let i = 0; i < nodeNum; i++) {
            this.neighborsRssiTtl.push([0.0, 0]);
        }

        this.data = this.generateData();
        this.downloadData = [];

        this.sendNum = 0;
        this.sendSrcNum = 0;
        this.sendHandNum = 0;
        this.sendTransNum = 0;
        this.recvHandNum = 0;
        this.recvDataNum = 0;
        this.maxHop = 0;

        this.canvas = canvas;
        this.pwrRad = pwrRad * 45;
        this.x = x * 10 + 5;
        this.y = y * 10 + 5;
        this.color = LevColor[0];
        this.bkColor = LevBkColor[0];
        this.ctx = canvas.getContext('2d');
        this.speed = 0;
        this.angle = 0;

        this.superframeState = {
            currentSuperframe: 0, // 当前超帧编号
            capStart: 0, // CAP 开始时间
            cfpStart: CAP_DURATION, // CFP 开始时间
            inactiveStart: CAP_DURATION + CFP_DURATION, // 低功耗模式开始时间
            superframeEnd: SUPERFRAME_DURATION // 超帧结束时间
        };
        this.backoffTime = MIN_BACKOFF_TIME; // 当前退避时间
        this.backoffAttempts = 0; // 退避尝试次数

        this.kalmanFilter = new KalmanFilter(10, 0.1); // 初始化卡尔曼滤波
        this.kalmanFilter.state = [x, y, 0, 0]; // 初始化状态 [x, y, vx, vy]
        this.predictedPosition = [x, y]; // 预测位置
        this.x = x*10+5; // 当前x位置
        this.y = y*10+5; // 当前y位置
    }
    generateInitialEnergy() {
        const MIN_ENERGY = 50; // 最小初始能量
        const MAX_ENERGY = 100; // 最大初始能量
        return Math.floor(Math.random() * (MAX_ENERGY - MIN_ENERGY + 1)) + MIN_ENERGY;
    }



    move() {
        // 根据速度和方向更新位置
        this.x += this.speed * Math.cos(this.angle);
        this.y += this.speed * Math.sin(this.angle);

        // 限制节点在画布内移动
        if (this.x < 5) {
            this.x = 5;
            this.angle = Math.PI - this.angle; // 反弹
        } else if (this.x > 1115) {
            this.x = 1115;
            this.angle = Math.PI - this.angle; // 反弹
        }

        if (this.y < 5) {
            this.y = 5;
            this.angle = -this.angle; // 反弹
        } else if (this.y > 625) {
            this.y = 625;
            this.angle = -this.angle; // 反弹
        }
        if (Math.random() < 0.5) { // 5%的概率改变速度和方向
            this.speed = Math.random() * 8.0 + 0.5;
            this.angle = Math.random() * 2 * Math.PI;
        }
        // 更新卡尔曼滤波
        this.kalmanFilter.predict();
       // this.kalmanFilter.update([this.x, this.y]);

        // 预测未来位置
        this.predictedPosition = [
            this.kalmanFilter.state[0] + this.kalmanFilter.state[2] * 10, // 预测10步后的x位置
            this.kalmanFilter.state[1] + this.kalmanFilter.state[3] * 10  // 预测10步后的y位置
        ];
        

    }
    getDownloadData(){
        return this.downloadData;
    }

    setNodeAll(sNo,level,pwrRad,x,y,isSrc){
        this.canvas=canvas;
        this.sNo=sNo;
        this.level=level;
        this.pwrRad=pwrRad*45;
        this.x=x*10+5;
        this.y=y*10+5;
        this.isSrc=isSrc;
        this.color=LevColor[level];
        this.bkColor=LevBkColor[level];
    }

    setNo(sNo){
        this.sNo=sNo;
    }

    setLevel(level){
        this.color=LevColor[level];
        this.bkColor=LevBkColor[level];
    }
    
    resetHandShake(){
        this.handshaked=T_HANDSHAKE;
    }

    setRad(radius){
        this.pwrRad=radius*45;
    }

    setPosition(x,y){
        this.x=x*10+5;
        this.y=y*10+5;
    }

    setIsSrc(b){
        this.isSrc=b;
    }

    isAPackC()
    {
        if(this.type==1)
            return true;
        else
            return false;
    }

    drawNode(type) {
        if (type === 'all' || type === 'pwrAera') {
            this.ctx.beginPath();
            this.ctx.fillStyle = this.bkColor;
            this.ctx.arc(this.x, this.y, this.pwrRad, 0, 2 * Math.PI);
            this.ctx.fill();
        }
    
        if (type === 'all' || type === 'core') {
            this.ctx.beginPath();
            this.ctx.fillStyle = this.color;
            this.ctx.arc(this.x, this.y, 5, 0, 2 * Math.PI);
            this.ctx.fill();
    
            this.ctx.beginPath();
            this.ctx.strokeStyle = this.color;
            this.ctx.lineWidth = 2;
            this.ctx.moveTo(this.x - 5, this.y - 10);
            this.ctx.lineTo(this.x + 45, this.y - 10);
            this.ctx.stroke();
    
            this.ctx.beginPath();
            this.ctx.fillStyle = this.color;
            this.ctx.font = "16px Arial";
            this.ctx.fillText(
                `${this.sNo}/${this.maxHop}/${this.sendNum - this.sendHandNum}/${this.recvDataNum}`, 
                this.x, 
                this.y - 14
            );
    
            // 对源节点进行特殊化显示
            if (this.isSrc) {
                // 绘制大红色五角星标记
                this.ctx.beginPath();
                this.ctx.fillStyle = "red";
                this.ctx.moveTo(this.x + 15, this.y - 10);
                this.ctx.lineTo(this.x + 25, this.y);
                this.ctx.lineTo(this.x + 15, this.y + 10);
                this.ctx.lineTo(this.x + 5, this.y + 5);
                this.ctx.lineTo(this.x + 5, this.y - 5);
                this.ctx.closePath();
                this.ctx.fill();
    
                // 使用黄色字体显示 "源节点" 标签
                this.ctx.font = "12px Arial";
                this.ctx.fillStyle = "yellow";
                this.ctx.fillText("源节点", this.x + 30, this.y);
            }
        }
    }

    tickWaitFifo(){
        let len=this.waitSendFifo.length;
        if(len==0)
            return;
        for(let i=len-1;i>=0;i--)
        {
            let [s,t]=this.waitSendFifo[i];
            t++;
            if(t>=MAX_SEND_TEMP_TIMEO)
                this.waitSendFifo.splice(i,1);
            else
                this.waitSendFifo[i]=[s,t];
        }
    }

    insertWaitFifo(s){
        let len=this.waitSendFifo.length;
        if(len>=MAX_SEND_TEMP_STORE)
            this.waitSendFifo.pop();
        s.lastNode=this.sNo;
        s.x=this.x;
        s.y=this.y;
        this.waitSendFifo.unshift([s,0]);
    }

    updateWaitItemDes(waitDes,recvPackDes){  //每收到1包，把先前待转发的des更新
        let ret='IN';
        let len=waitDes.length;
        if(len!=recvPackDes.length)
            return 'NONE';

        for(let i=0;i<len;i++)
        {
            if(waitDes[i]==1 || recvPackDes[i]==1)
                waitDes[i]=1;
        }

        for(let i=0;i<len;i++)
        {
            if(waitDes[i]==0)
            {
                ret='DEL';
                break;
            }
        }

        return ret;
    }

    isInWaitFifo(src,id,recvPackDes){
        let ret=false;
        let len=this.waitSendFifo.length;
        if(len==0)
            return true;
        for(let i=len-1;i>=0;i--)
        {
            let [ss,dd]=this.waitSendFifo[i];
            if(src==ss && id==dd)
            {
                let result=updateWaitItemDes(ss.des,recvPackDes);
                if(result=='NONE')
                    continue;    
                else if(result=='DEL')
                    this.waitSendFifo.splice(i,1);
                ret=true;
                break;
            }
        }

        return true;
    }
    
    generateData() //return DATA_LEN array
    {
        let ret=[];
        let n=this.sNo*100+this.id*DATA_LEN;
        for(let i=0;i<DATA_LEN;i++)
        {
            //let n=Math.round(Math.cos(sNo*(id*44+i)*2*PI/880)*255);
            //let n=Math.round(Math.cos(sNo*(id*44+i)*2*PI/880)*255);
            ret.push(n+i);
        }
    
        return ret;
    }

    eitherSrc_WaitItem()
    {
        let msg,msgSrc,msgWait;
        if(this.isSrc)
        {
            msgSrc=new msgPack(0,this.sNo,this.x,this.y);
            msgSrc.volumn=this.volumn;
            msgSrc.des[this.sNo-1]=1;
            
            msgSrc.data.length=0;
            msgSrc.data=this.generateData();
            this.id++;
            if(this.id>=ALL_DATA_PACK_NUM)
                this.id=0;
        }
        let len=this.waitSendFifo.length;
        if(len>0)
        {
            msgWait=this.waitSendFifo[len-1];
            if(msgSrc.volumn>=msgWait.volumn)
                msg=msgSrc;
            else
            {
                msg=msgWait;
                this.waitSendFifo.pop();
            }
        }

        return msg;
    }
    
    createAPackC()
    {
        let sC=new msgPack(1,this.sNo,this.x,this.y);
        insertWaitFifo(sC);
    }

    setANeighbor(nNo,rssi,nodeNum){
        if(nNo>0 && nNo<=nodeNum)
        {
            let item=[rssi,TTL_NEIGHBOR];
            this.neighborsRssiTtl[nNo-1]=item;
        }
    }

    tickNeighbors(){
        let len=this.neighborsRssiTtl.length;
        for(let i=len-1;i>=0;i--)
        {
            if(i==this.sNo-1)
                continue;
            let [s,t]=this.neighborsRssiTtl[i];
            if(t>0 && t<=DELAY_FOR_HANDSHAKE)
            {
                t--;
                if(t==0)
                    this.neighborsRssiTtl[i]=[0.0,0];
                else
                    this.neighborsRssiTtl[i]=[s,t];
            }
        }
    }

    tickJustRecv(){
        let len=this.justRecvedPacks.length;
        if(len==0)
            return;
        for(let i=len-1;i>=0;i--)
        {
            let [src,id,t]=this.justRecvedPacks[i];
            t++;
            if(t>=MAX_JUST_RECVED_TIMEO)
                this.justRecvedPacks.pop();
            else
                this.justRecvedPacks[i]=[src,id,t];
        }
    }

    insertJustRecv(src,id){
        this.justRecvedPacks.unshift([src,id,0]);
    }

    isInJustRecv(src,id){
        let ret=false;
        let len=this.justRecvedPacks.length;
        if(len==0)
            return ret;
        for(let i=0;i<len;i++)
        {
            let [s,d,t]=this.justRecvedPacks[i];
            if(src==s && id==d)
            {
                ret=true;
                break;
            }
        }

        return ret;
    }

    capBehavior() {
        // 检查是否有数据待发送
        if (this.waitSendFifo.length > 0) {
            const [msgPack, timestamp] = this.waitSendFifo[0]; // 获取待发送的数据包

            // 检查信道是否忙
            if (myNeighborSending(this.x, this.y, this.pwrRad)) {
                // 如果信道忙，执行退避机制
                this.backoff();
            } else {
                // 如果信道空闲，尝试发送数据
                this.sendData(msgPack); // 发送数据
                this.resetBackoff(); // 重置退避机制
            }
        } else {
            console.log(`Node ${this.sNo} has no data to send.`);
        }
    }
    backoff() {
        // 计算退避时间
        this.backoffTime = Math.min(MAX_BACKOFF_TIME, this.backoffTime * BACKOFF_EXPONENTIAL_INCREASE);
        this.backoffAttempts++;

        console.log(`Node ${this.sNo} is backing off for ${this.backoffTime} ticks.`);

        // 在退避时间后再次尝试发送
        setTimeout(() => {
            this.capBehavior(); // 重新进入 CAP 行为
        }, this.backoffTime * SIMU_TICK);
    }

    resetBackoff() {
        this.backoffTime = MIN_BACKOFF_TIME; // 重置退避时间
        this.backoffAttempts = 0; // 重置退避尝试次数
    }

    attemptToSendData() {
        // 检查是否有数据待发送
        if (this.waitSendFifo.length > 0) {
            const [msgPack, timestamp] = this.waitSendFifo[0]; // 获取待发送的数据包
            console.log(`Node ${this.sNo} is attempting to send data: ${msgPack.id}`);
            this.sendData(msgPack); // 发送数据
        } else {
            console.log(`Node ${this.sNo} has no data to send.`);
        }
    }

    sendData(msgPack) {
        // 发送数据包：将数据包加入空中信号队列
        rxtxQue.push(msgPack);
        console.log(`Node ${this.sNo} sent data: ${msgPack.id}`);
        // 更新节点状态：发送次数增加
        this.sendNum++;
        if (msgPack.src === this.sNo) {
            this.sendSrcNum++;
        } else {
            this.sendTransNum++;
        }
    }

    cfpBehavior() {
        // 在 CFP 期间，设备可以进行无竞争的通信
        // 实现无竞争通信逻辑
        this.attemptToSendData();
    }

    inactiveBehavior() {
        // 在 Inactive Period，节点进入低功耗模式
        console.log(`Node ${this.sNo} is in Inactive Period.`);
        // 可以在此处实现低功耗模式的逻辑，例如降低能量消耗
        this.energy -= ENERGY_CONSUMPTION_IDLE; // 简化的低功耗模式能量消耗
    }

    
}

const DATA_LEN=2;  //104;    
var rxtxQue=[];        //收-发空中信号存放区,msgPack为成员
class msgPack{
    constructor(type,src,x,y){
        this.type=type;
        this.src=src;
        this.id=0;
        this.lastNode=0;
        this.hop=0;
        this.volumn=0;
        this.des=[];    //取决于pub_totle_nodes
        for(let i=0;i<pub_totle_nodes;i++)
            this.des.push(0);
        this.data=[];   //体部数据DATA_LEN,实际=104字节，仿真取10
        for(let i=0;i<DATA_LEN;i++)
            this.data.push(0);
    
        this.x=x;       //用于位置显示、计算RSSI
        this.y=y;
    }
}

var pub_totle_nodes;        
var pub_radius;        
var pub_src;        
var pub_result;    

var pub_tick=0;     //总仿真时间计数
const PUB_TICK_STARTING=50; //在此期限内，只发出C包，用于初始的邻居发现

//------基本函数---------------------------
function setLocalStorage(item,ss){  //本地信息写
    if(typeof(Storage)=="undefined")
        return;        //不支持 web 存储
    localStorage.setItem(item, ss);        
}
    
function getLocalStorage(item){ //本地信息读
    if(typeof(Storage)=="undefined")
        return;        //不支持 web 存储
    return localStorage.getItem(item);
}

function get32Color(colorIndex, alpha) { //24种梯度颜色，R-G-B-R
    let r,g,b;
    if(colorIndex>=1 && colorIndex<9)
    {
        r=Math.round((9-colorIndex)/8*255);
        if(r>255)
            r=255;
        g=255-r;
        b=0;
    }
    else if(colorIndex>=9 && colorIndex<17)
    {
        g=Math.round((17-colorIndex)/8*255);
        if(g>255)
            g=255;
        b=255-g;
        r=0;
    }
    else if(colorIndex>=17 && colorIndex<25)
    {
        b=Math.round((25-colorIndex)/8*255);
        if(b>255)
            b=255;
        r=255-b;
        g=0;
    }
    else
        return '';

    return 'rgba('+r.toString()+','+g.toString()+','+b.toString()+','+alpha.toString()+')';
}

function getRandomInt(min, max) {   //产生随机数，用于节点散布
    min = Math.ceil(min);
    max = Math.floor(max);
    return Math.floor(Math.random() * (max - min + 1)) + min;
}

function panelDisp(whom,b){  //组件是否显示，en/dis
    var x=document.getElementById(whom);
    if(b==='en')
        x.style="visibility: visible";
    else if(b==='dis')
        x.style="visibility: hidden";

//    $("#"+whom).load(location.href+" #"+whom+">*","");
}

//---初始化-----------------------------
function onLoad()   //---读取公共参数并显示，清空画布
{
    document.getElementById('id-totle-sel-ten').selectedIndex=0;
    document.getElementById('id-totle-sel-one').selectedIndex=0;
    document.getElementById('id-radius-sel').selectedIndex=0;
        
    getLocalData();

    if(pub_totle_nodes!='' && pub_radius!=null)
    {
        document.getElementById('id-totle-nodes-radius').innerHTML='-'+pub_totle_nodes+'-'+pub_radius+'-';
        
        let ten=parseInt(pub_totle_nodes.substring(0,1));
        let one=parseInt(pub_totle_nodes.substring(1));
        document.getElementById('id-totle-sel-ten').selectedIndex=ten;
        document.getElementById('id-totle-sel-one').selectedIndex=one;
    
        let rad=parseInt(pub_radius);
        document.getElementById('id-radius-sel').selectedIndex=rad;
    }else{
        document.getElementById('id-totle-nodes-radius').innerHTML='-XX-X-';
    }

    if(pub_src=='')
        document.getElementById('id-textaera-srcs').innerHTML='------';
    else
        document.getElementById('id-textaera-srcs').innerHTML=pub_src;
    
    document.getElementById('id-src-add-one').selectedIndex=1;
    
    if(pub_result=='')
        document.getElementById('id-textaera-result').innerHTML='------';
    else
        document.getElementById('id-textaera-result').innerHTML=pub_result;

    canvasInit()
    document.getElementById('id_simu_stop').disabled = true;

}

//---函数集：本地参数存取----------------
function getLocalData(){
    pub_totle_nodes=getLocalStorage('totleNodes');
    pub_radius=getLocalStorage('radius');
    pub_src=getLocalStorage('srcGroup');
    pub_result=getLocalStorage('lastResult');
}

function setLocalData(whom,val){
    if(whom==null)
    {
        setLocalStorage('totleNodes',pub_totle_nodes);
        setLocalStorage('radius',pub_radius);
        setLocalStorage('srcGroup',pub_src);
        setLocalStorage('lastResult',pub_result);
    }
    else
        setLocalStorage(whom,val);
}

function storeParam(pam){
    if(pam=='totleNodesRadius')
    {
        let sel10=document.getElementById('id-totle-sel-ten');
        let sel1=document.getElementById('id-totle-sel-one');
        let selrad=document.getElementById('id-radius-sel');
        let ten=sel10.options[sel10.selectedIndex].value;
        let one=sel1.options[sel1.selectedIndex].value;
        let rad=selrad.options[selrad.selectedIndex].value;
        
        let txt=document.getElementById('id-totle-nodes-radius');
        if(ten=='0' && one=='0')
        {
            alert('总点数必须大于0');
            return false;
        }
        else 
        {
            if(parseInt(ten+one)>24)
            {
                alert('总点数不能大于24');
                return false;
            }
            let w='-'+ten+one+'-'+rad+'-';
            txt.innerHTML=w;
            pub_totle_nodes=(ten+one).toString();
            pub_radius=rad;
            setLocalData('totleNodes',ten+one);
            setLocalData('radius',rad);
        }
    }else if(pam=='srcGroup'){
        let src=document.getElementById('id-textaera-srcs');
        pub_src=src.innerHTML;
        if(pub_src=='------')
            pub_src='';
        setLocalData('srcGroup',pub_src);
    }else if(pam=='lastResult'){
        let res=document.getElementById('id-textaera-result');
        pub_result=res.innerHTML;
        setLocalData('lastResult',pub_result);
    }

    return true;
}

//---函数集：图形显示-------------------
function canvasInit()   //设置画布尺寸，并清空
{
    var canvas=document.getElementById('desktop');
    canvas.width=1120;
    canvas.height=630;
    clearCanvas(canvas,0,0,canvas.width,canvas.height);
}

function clearCanvas(cvs,x0,y0,x1,y1)   //清空画布
{
    if(cvs==null)
    {
        alert("no canvas");
        return;
    }
    var scn=cvs.getContext('2d');
    scn.fillStyle='#000000';
    scn.fillRect(x0,y0,x1,y1);
}

//---函数集：站点创建和参数（调整）设置---------
function setupAllNodes() {
    if (!storeParam('totleNodesRadius'))
        return;
    if (pub_totle_nodes == 0)
        return;

    document.getElementById('id-textaera-srcs').innerHTML = '';
    document.getElementById('id-textaera-result').innerHTML = '';
    pub_src = '';
    pub_result = '';

    LevColor.length = 0;
    LevBkColor.length = 0;
    LevColor.push('rgba(192,192,192,1.0)');
    LevBkColor.push('rgba(192,192,192,0.2)');

    for (let i = 1; i <= pub_totle_nodes; i++) {
        let num = Math.round(i * 24 / pub_totle_nodes);
        LevColor.push(get32Color(num, 1.0, pub_totle_nodes));
        LevBkColor.push(get32Color(num, 0.2, pub_totle_nodes));
    }

    var canvas = document.getElementById('desktop');
    let x0 = 0;
    let y0 = 5;
    let index = 1;
    let row = Math.floor(parseInt(pub_totle_nodes) / 10) + 1;
    let leftCol = parseInt(pub_totle_nodes) % 10;

    canvasInit();
    let item;
    Nodes.length = 0;
    for (let i = 0; i < row; i++) {
        x0 = 5;
        if (i < row - 1) {
            for (let j = 0; j < 10; j++) {
                item = new devNode(canvas, index, pub_radius, x0, y0, 0, pub_totle_nodes);
                // 设置随机速度和方向
                item.speed = Math.random() * 8.0 + 0.5; // 速度范围
                item.angle = Math.random() * 2 * Math.PI; // 随机方向
                x0 += 10;
                index++;
                Nodes.push(item);
            }
            y0 += 10;
        } else {
            for (let j = 0; j < leftCol; j++) {
                item = new devNode(canvas, index, pub_radius, x0, y0, 0, pub_totle_nodes);
                // 设置随机速度和方向
                item.speed = Math.random() * 0.5 + 0.1; // 速度范围0.1-0.6
                item.angle = Math.random() * 2 * Math.PI; // 随机方向
                x0 += 10;
                index++;
                Nodes.push(item);
            }
        }
    }

    Nodes.forEach(element => {
        element.drawNode('all');
    });
}

function deployNodes(pam){  //节点散布，或重绘半径
    let len=Nodes.length;
    if(len==0){
        alert('没有节点可以部署')
        return;
    }

    let ptX=[];
    let ptY=[];
    if(pam=='rand-positon')
    {
        clearAllNodesLevel();
        for(let j=0;j<len;j++)
        {
            for(;;)
            {
                let randomIntX = getRandomInt(5, 108);
                let randomIntY = getRandomInt(5, 61);
                if(!hadExist(randomIntX,randomIntY,ptX,ptY))
                {
                    ptX.push(randomIntX);
                    ptY.push(randomIntY);
                    break;
                }
            }
        }

        for(let i=0;i<len;i++)
            Nodes[i].setPosition(ptX[i],ptY[i]);
    }

    canvasInit();
    Nodes.forEach(item => {
        item.drawNode('pwrAera');
    });

    Nodes.forEach(item => {
        item.drawNode('core');
    });
}

function showParam(type){   
    if(type=='totleNodesRadius')
    {
        if(pub_totle_nodes!='' && pub_radius!='')
            document.getElementById('id-totle-nodes-radius').innerHTML='-'+pub_totle_nodes+'-'+pub_radius+'-';
        else
            document.getElementById('id-totle-nodes-radius').innerHTML='-XX-X-';
    }else if(type=='srcGroup'){
        if(pub_src!='')
            document.getElementById('id-textaera-srcs').innerHTML=pub_src;
        else
            document.getElementById('id-textaera-srcs').innerHTML='------';
    }else if(type=='lastResult'){
        if(pub_result!='')
            document.getElementById('id-textaera-result').innerHTML=pub_result;
        else
            document.getElementById('id-textaera-result').innerHTML='------';
    }
}

function updateRadius(){    //修改功率半径，图形跟随变化
    let txt=document.getElementById('id-totle-nodes-radius').innerHTML;
    let n=txt.lastIndexOf('-');
    txt=txt.substring(0,n);
    n=txt.lastIndexOf('-');
    txt=txt.substring(0,n+1);
    let sel=document.getElementById('id-radius-sel');
    let rad=sel.options[sel.selectedIndex].value;
    txt += rad+'-';
    document.getElementById('id-totle-nodes-radius').innerHTML=txt;
    pub_radius=rad;
    setLocalData('radius',rad);

    Nodes.forEach(item => {
        item.setRad(rad);
        item.setLevel(0);
    });

    deployNodes();
}

function srcSet(type){      //设置发送源，即讲话者
    var ss;
    var len;
    var sel10=document.getElementById('id-src-add-ten');
    var sel1=document.getElementById('id-src-add-one');
    var vol0=document.getElementById('id-src-volumn');
    var vol=vol0.options[vol0.selectedIndex].value;
    var ten=sel10.options[sel10.selectedIndex].value;
    var one=sel1.options[sel1.selectedIndex].value;
    var ele0=parseInt(ten+one);
    var ss0;
    var ss1;
    var bRet=false;

    switch(type)
    {
        case 'add-one':
            if(ele0>parseInt(pub_totle_nodes) || ele0==0)
            {
                alert('序号必须小于等于总点数，并且不能为0')
                return;
            }

            ss=pub_src.split(",");
            len=ss.length;
            if(ss[0]=='')
                ss.splice(0,1);
            len=ss.length;
            ss.forEach(element => {
                let s=element.split('_');
                let n=parseInt(s[0]);
                ss0=n;
                if(ss0==ele0)
                {
                    alert('该元素已在集合中');
                    bRet=true;
                    return;
                }
            });
            if(bRet)
                break;

            if(len>24)
            {
                alert('不能再添加元素了');
                return;
            }
            if(len==0)
                ss.unshift(ele0.toString()+'_'+vol.toString());
            else if(len==1){
                ss0=parseInt(ss[0]);
                if(ele0<ss0)
                    ss.unshift(ele0.toString()+'_'+vol.toString());
                else
                    ss.push(ele0.toString()+'_'+vol.toString());
            }else{
                ss0=parseInt(ss[0]);
                if(ele0<ss0)
                    ss.unshift(ele0.toString()+'_'+vol.toString());
                else
                {
                    ss0=parseInt(ss[len-1]);
                    if(ele0>ss0)
                        ss.push(ele0.toString()+'_'+vol.toString());
                    else
                    {
                        for(let i=0;i<len-1;i++)
                        {
                            ss0=parseInt(ss[i]);
                            ss1=parseInt(ss[i+1]);
                            if(ele0>ss0 && ele0<ss1)
                            {
                                ss.splice(i+1,0,ele0.toString()+'_'+vol.toString()); 
                                break;   
                            }
                        }
                    }
                }
            }
            
            pub_src='';
            ss.forEach(element => {
                pub_src += element+',';    
            });

            len=pub_src.length;
            if(pub_src.lastIndexOf(',')==len-1)
                pub_src=pub_src.substring(0,len-1);

            showParam('srcGroup');
            storeParam('srcGroup');
            break;

        case 'sub-one':
            if(ele0>parseInt(pub_totle_nodes) || ele0==0)
            {
                alert('序号必须小于等于总点数，并且不能为0')
                return;
            }

            ss=pub_src.split(',');
            len=ss.length;
            if(len==1 && ss[0]=='')
                len=0;
            if(len==0)
            {
                alert('没有可去除的元素');
                return;
            }
            for(let i=0;i<len;i++)
            {
                ss0=parseInt(ss[i]);
                if(ele0==ss0)
                {
                    ss.splice(i,1); 
                    bRet=true;
                    break;   
                }
            }
  
            if(!bRet)
            {
                alert('该元素不在集合中');
                return;
            }

            len=ss.length;
            pub_src='';
            for(let i=0;i<len;i++)
            {
                if(i<len-1)
                    pub_src += ss[i]+',';
                else
                    pub_src += ss[i];
            }

            len=pub_src.length;
            if(len>0 && (pub_src.lastIndexOf(',')==len-1))
                pub_src=substring(0,len-1);

            showParam('srcGroup');
            storeParam('srcGroup');
            break;
                        
        case 'sub-all':
            pub_src='';
            showParam('srcGroup');
            storeParam('srcGroup');
            break;
                            
    }

}

function hadExist(x,y,ptX,ptY){ //产生节点时，避免2个点在同一个坐标上
    let b=false;
    let len=ptX.length;

    for(let i=0;i<len;i++)
    {
        if(x===ptX[i] && y===ptY)
        {
            b=true;
            break;
        }
    }

    return b;
}

function clearAllNodesLevel(){  //所有节点置灰色，重设功率半径、重新散布，调用此函数
    Nodes.forEach(element => {
        element.setLevel(0);
    });
}

function getRssi(x0,y0,x,y,rad) //将节点距离转换为RSSI，用于邻居发现
{
    let d=Math.sqrt((x-x0)*(x-x0)+(y-y0)*(y-y0));
    if(d<rad)
    {
        if(d<rad*0.1)
            return 1.0;
        else
            return 1.0-d/rad;
    }
    else
        return 0;
}

//---函数集：包处理，包括包与节点关系-----
function iRecvedIt(src,nodeX,nodeY,nodePwrRad,msg){ //是我可以收到的包，即他是我的邻居
    if(src==msg.src || (nodeX==msg.x && nodeY==msg.y))    //是自己发的包，剔除
        return  [false,0.0];
    let rssi=getRssi(nodeX,nodeY,msg.x,msg.y,nodePwrRad);
    if(rssi>0)
        return [true,rssi];
    else
        return [false,0.0];
}

function myNeighborSending(x0, y0, rad) {
    let ret = false;
    let len = rxtxQue.length;
    for (let i = 0; i < len; i++) {
        if (getRssi(x0, y0, rxtxQue[i].x, rxtxQue[i].y, rad) > 0) {
            ret = true;
            break;
        }
    }
    return ret;
}

function atPackDesEnd(msg, nodeSNo, nodeNeighbors)
 {
    let end = true; // 当前节点置1，若des为0但邻居为1且能量充足，则将对应0置1，然后发送；否则结束转发
    msg.des[nodeSNo - 1] = 1;

    for (let i = 0; i < nodeNeighbors.length; i++) {
        let [rssi, ttl] = nodeNeighbors[i];
        if (msg.des[i] == 0 && rssi > 0 && Nodes[i].energy > Nodes[i].energyThreshold) {
            msg.des[i] = 1;
            end = false;
        }
    }

    return end;
}

function mergePackDes(msg, nodeRssi) {
    let len = nodeRssi.length;
    for (let i = 0; i < len; i++) {
        let [rssi, ttl] = nodeRssi[i];
        if (rssi > 0 && Nodes[i].energy > Nodes[i].energyThreshold) {
            msg.des[i] = 1;
        }
    }
}

//---函数集：仿真-----------------------
function doSimu() {
    initSimuParam();
    deployNodes();  // 节点颜色置黑白

    // ---确定源及音量-----
    let srcG = pub_src.split(',');
    let lenSrc = srcG.length;
    if (lenSrc == 1 && srcG[0] == '') {
        lenSrc = 0;
        alert('缺少发送源，不能运行');
        return;
    }

    for (let i = 0; i < lenSrc; i++) {
        let s = srcG[i].split('_');
        let nNo = parseInt(s[0]);
        let vol = parseInt(s[1]);
        Nodes[nNo - 1].volumn = vol;
        Nodes[nNo - 1].isSrc = true;
    }

    // ---按节拍开始仿真-------------
    var tickTotle = 0;     // 总节拍数
    setTimeout(
        function stepSimu()
         {
        if (tickTotle < ALL_STEPS_THESHOLD) {
            tickTotle++;
        } else {
            alert('仿真结束---总步数超限');
            showResult();
            return;
        }

        for (let j = 0; j < pub_totle_nodes; j++) {
            
            let srcPack, transPack;

            let node = Nodes[j];

            // 更新超帧状态
            node.superframeState.currentSuperframe = Math.floor(tickTotle / SUPERFRAME_DURATION);
            let currentTickInSuperframe = tickTotle % SUPERFRAME_DURATION;

            if (currentTickInSuperframe >= node.superframeState.capStart && currentTickInSuperframe < node.superframeState.cfpStart) {
                // CAP 期间的行为
                node.capBehavior();
            } else if (currentTickInSuperframe >= node.superframeState.cfpStart && currentTickInSuperframe < node.superframeState.inactiveStart) {
                // CFP 期间的行为
                node.cfpBehavior();
            } else if (currentTickInSuperframe >= node.superframeState.inactiveStart && currentTickInSuperframe < node.superframeState.superframeEnd) {
                // 低功耗模式
                node.inactiveBehavior();
            }

              // 检查节点状态（是否能量耗尽）
              checkNodeStatus(node);

              // 如果能量不足，跳过该节点的后续操作
              if (node.energy <= node.energyThreshold) {
                  continue;
              }
  
              // 更新节点的空闲能量消耗
              tickIdle(node);
            
            node.move(); // 调用节点移动方法
            node.tickNeighbors();   // 按时计数和更新
            node.tickWaitFifo();    // 按时计数和更新
            node.tickJustRecv();    // 按时计数和更新

            if (node.handshaked > 0)
                node.handshaked--;
            if (node.nPermittedSend > 0)
                node.nPermittedSend--;
            if (node.nPermittedSend == 0)  // 源节点或握手请求，生成1个待发数据包，将来可能会被转发包覆盖。初始时，留一段时间用于建立邻居关系
            {
                if (node.isSrc) {
                    srcPack = new msgPack(0, node.sNo, node.x, node.y);
                    mergePackDes(srcPack, node.neighborsRssiTtl);

                    srcPack.id = node.id;
                    srcPack.data = node.generateData();
                    node.id++;

                    srcPack.lastNode = node.sNo;
                    srcPack.volumn = node.volumn;
                } else if (node.handshaked == 0) {
                    srcPack = new msgPack(1, node.sNo, node.x, node.y);
                    srcPack.id = PACK_C_ID;
                    srcPack.lastNode = node.sNo;
                    let spLen = srcPack.des.length;
                    for (let k = 0; k < spLen; k++)
                        srcPack.des[k] = 1;
                }
            }

            let lenRTQ = rxtxQue.length;  // 查看空中信号处理转发事务
            for (let i = 0; i < lenRTQ; i++) {
                let rtItem = { ...rxtxQue[i] };
                let [b, rss] = iRecvedIt(node.sNo, node.x, node.y, node.pwrRad, rtItem);
                if (b) {
                    node.setANeighbor(rtItem.lastNode, rss, pub_totle_nodes); // 动态更新邻居列表

                    if (rtItem.type == 0)  // data pack
                    {
                        if (!node.isInJustRecv(rtItem.src, rtItem.id)) {
                            var ss, idid;
                            ss = rtItem.src;
                            idid = rtItem.id;
                            node.recvDataNum++;
                            node.insertJustRecv(ss, idid); // 计入最近接收队列
                            node.setLevel(ss);  // 显示新颜色
                            var dd = [];
                            for (let k = 0; k < rtItem.data.length; k++)
                                dd.push(rtItem.data[k]);
                            node.downloadData = node.downloadData.concat(dd); // 收到的内容保留下来，即话音
                            rtItem.hop++;
                            if (node.maxHop < rtItem.hop)
                                node.maxHop = rtItem.hop;
                            if (!atPackDesEnd(rtItem, node.sNo, node.neighborsRssiTtl)) // 是否已转发到末端
                            {
                                if (rtItem.hop < MAX_HOP) {
                                     // 选择下一个节点
                                     let possibleNodes = Nodes.filter(n => n.sNo !== node.sNo && n.energy > n.energyThreshold);
                                     let nextNode = selectNextNode(node, possibleNodes, alpha, beta);
                                    rtItem.lastNode = nextNode.sNo;
                                    transPack = rtItem;
                                }
                            }
                        }
                    }
                }
            }

            if (transPack != null && srcPack != null) {
                if (srcPack.type == 0) // data Pack
                {
                    if (srcPack.volumn > transPack.volumn)
                        transPack = srcPack;
                }
            } else if (srcPack != null)
                transPack = srcPack;

            if (transPack == null) // 此节点无新产生的待发数据
                continue;

            let fifoLen = node.waitSendFifo.length;
            if (fifoLen == 0)
                node.insertWaitFifo(transPack); // 加入待发队列
            else if (fifoLen == 1) {
                let [s, t] = node.waitSendFifo[0];
                if (s.type == 1) {
                    node.waitSendFifo.pop();
                    node.insertWaitFifo(transPack); // 加入待发队列
                }
            } else if (transPack.type == 0)
                node.insertWaitFifo(transPack); // 加入待发队列

                 // 更新信息素
                 //console.log(`transPack.lastNode 的值为：${transPack.lastNode}`);
                 //console.log(`Nodes 数组的长度为：${Nodes.length}`);
                                  // 假设这是数据包传输逻辑的一部分


                                  for (let i = 0; i < pub_totle_nodes; i++) {
                                    
                                        
                                            let srcNode = Nodes[i];
                                            let destNode = Nodes[transPack.lastNode - 1];
                                            console.log(`准备更新信息素：从节点 ${srcNode.sNo} 到节点 ${destNode.sNo}`);
                                            updatePheromone(srcNode, destNode, ENERGY_CONSUMPTION_SEND, Q, rho);
                                        
                                    }
                  /*
                 let destNode = Nodes[transPack.lastNode - 1];
                   console.log(`准备更新信息素：从节点 ${node.sNo} 到节点 ${destNode.sNo}`);
                    updatePheromone(node, destNode, ENERGY_CONSUMPTION_SEND, Q, rho);
                    
                      for (let i = 0; i < pub_totle_nodes; i++) {
                        for (let j = 0; j < pub_totle_nodes; j++) {
                            if (i !== j) {
                                let srcNode = Nodes[i];
                                let destNode = Nodes[transPack.lastNode - 1];
                                console.log(`准备更新信息素：从节点 ${srcNode.sNo} 到节点 ${destNode.sNo}`);
                                updatePheromone(srcNode, destNode, ENERGY_CONSUMPTION_SEND, Q, rho);
                            }
                        }}
                    
                    */

        }
       
        evaporatePheromone(rho);// 蒸发信息素
        

        rxtxQue.length = 0;   // 处理待发事务
        for (let j = 0; j < pub_totle_nodes; j++) {
            let node = Nodes[j];
            if (node.nPermittedSend > 0) {
                node.nPermittedSend--;
                continue;
            }

            if (!myNeighborSending(node.x, node.y, node.pwrRad))    // 隐含引用rxtxQue
            {
                let wlen = node.waitSendFifo.length;
                if (wlen > 0) {
                    let [msgPack, t] = node.waitSendFifo[wlen - 1];
                    var sd = { ...msgPack };
                    rxtxQue.push(sd);
                    node.waitSendFifo.pop();
                    node.handshaked = T_HANDSHAKE;
                    node.nPermittedSend = NO_SEND;
                    if (msgPack.src == node.sNo && msgPack.type == 0)
                        node.setLevel(node.sNo);  // 显示新颜色

                    node.sendNum++;
                    if (msgPack.src == node.sNo) {
                        if (msgPack.type == 0)
                            node.sendSrcNum++;
                        else
                            node.sendHandNum++;
                    } else
                        node.sendTransNum++;
                }
            }
        }

        deployNodes();
        setTimeout(stepSimu, SIMU_TICK);
        
    }
    , SIMU_TICK);
    function stopSimu() {
        simulationRunning = false;
        document.getElementById('id_simu_stop').disabled = true;
        showResult();
}}
function initSimuParam(){


    pheromoneMatrix = [];
    etaMatrix = [];

    for (let i = 0; i < pub_totle_nodes; i++) {
        pheromoneMatrix[i] = [];
        etaMatrix[i] = [];
        for (let j = 0; j < pub_totle_nodes; j++) {
            pheromoneMatrix[i][j] = 1; // 初始信息素浓度
            //etaMatrix[i][j] = 1 / (getDistance(Nodes[i], Nodes[j]) + 1e-4); // 启发式信息，距离的倒数
            etaMatrix[i][j] = 1/(getDistance(Nodes[i], Nodes[j])/100) ;
        }
    }
    console.log("信息素矩阵初始化完成：", pheromoneMatrix);
    console.log("启发式信息矩阵初始化完成：", etaMatrix);


    rxtxQue.length=0;   //没有空中信号
    
    Nodes.forEach(element => {  //每个节点的运行数据清空
        element.id=0;
        element.isSrc=false;
        
        element.justRecvedPacks.length=0;
        element.nPermittedSend=0;
        element.waitSendFifo.length=0;
        element.handshaked=0;
        
        let len=element.neighborsRssiTtl.length;
        for(let i=0;i<len;i++)
            element.neighborsRssiTtl[i]=[0.0,0];
        element.neighborsRssiTtl[element.sNo-1]=[1.0,DELAY_FOR_HANDSHAKE+10];
        
        element.downloadData.length=0;
        
        element.sendNum=0;  
        element.sendHandNum=0;
        element.sendSrcNum=0;
        element.sendTransNum=0;
        element.recvDataNum=0;
        element.recvHandNum=0;
        element.maxHop=0;

        element.color=LevColor[0];
        element.bkColor=LevBkColor[0];
        element.backoffTime = MIN_BACKOFF_TIME; // 初始化退避时间
        element.backoffAttempts = 0; // 初始化退避尝试次数
    });
}
function showResult() {
    let result = document.getElementById('id-textaera-result');
    result.innerHTML = '';  // 清空网页中的显示内容
    let output = '';  // 用于存储终端输出的内容

    for (let i = 0; i < pub_totle_nodes; i++) {
        let nodeInfo = `${i + 1}:\n`;
        nodeInfo += `   总发送次数 ${Nodes[i].sendNum}\n`;
        nodeInfo += `   源发送次数 ${Nodes[i].sendSrcNum}\n`;
        nodeInfo += `   握手发送次数 ${Nodes[i].sendHandNum}\n`;
        nodeInfo += `   转发次数 ${Nodes[i].sendTransNum}\n`;
        nodeInfo += `   最大跳数 ${Nodes[i].maxHop}\n`;
        nodeInfo += `   收到数据 ${Nodes[i].downloadData.length}\n`;
        nodeInfo += `   当前能量 ${Nodes[i].energy}\n`;
        nodeInfo += `   初始能量 ${Nodes[i].initialEnergy}\n`;

        // 邻居列表信息
        let neighbors = '';
        for (let j = 0; j < pub_totle_nodes; j++) {
            if (Nodes[i].neighborsRssiTtl[j][0] > 0) {
                neighbors += `${j + 1} (RSSI: ${Nodes[i].neighborsRssiTtl[j][0].toFixed(2)}) `;
            }
        }
        nodeInfo += `   邻居列表: ${neighbors}\n`;

        // 路由选择信息
        nodeInfo += `   路由选择信息:\n`;
        for (let j = 0; j < pub_totle_nodes; j++) {
            if (i !== j) {
                 // 生成0.1到0.3之间的随机值，并添加到信息素浓度上
        const randomValue = 0.1 + Math.random() * 0.2; // Math.random() 生成0到1之间的随机数
        
                nodeInfo += `      到节点 ${j + 1} 的信息素浓度: ${pheromoneMatrix[i][j].toFixed(2)}\n`;
                nodeInfo += `      到节点 ${j + 1} 的启发式信息: ${etaMatrix[i][j].toFixed(2)}\n`;
            }
        }
        // 数据内容
       nodeInfo += `   数据: ${Nodes[i].downloadData.join(',')}\n`;
        // 更新网页内容
        result.innerHTML += nodeInfo;
        // 输出到终端
        console.log(nodeInfo);
    }
}
//---函数集：备用-----------------
function isChild(last,curr,len){
    let ret=false;
    for(let i=0;i<len;i++)
    {
        if(last.substring(i,i+1)=='1' && curr.substring(i,i+1)=='1')
        {
            ret=true;
            break;
        }
    }
    return ret;
}

function tickIdle(node) {
    if (node.energy > node.energyThreshold) {
        node.energy -= ENERGY_CONSUMPTION_IDLE; // 空闲时的能量消耗
        console.log(`节点 ${node.sNo} 空闲，剩余能量: ${node.energy}`);
    } else {
        console.log(`节点 ${node.sNo} 能量不足，进入休眠状态`);
    }
}

function checkNodeStatus(node) {
    if (node.energy <= node.energyThreshold) {
        console.log(`节点 ${node.sNo} 能量耗尽，停止工作`);
        node.isSrc = false; // 如果是源节点，停止发送数据
        node.neighborsRssiTtl.fill([0.0, 0]); // 清空邻居列表
    }
}
function sendPacket(node) {
    if (node.energy > node.energyThreshold) {
        node.energy -= ENERGY_CONSUMPTION_SEND;
        console.log(`节点 ${node.sNo} 发送数据，剩余能量: ${node.energy}`);
    } else {
        console.log(`节点 ${node.sNo} 能量不足，无法发送数据`);
    }
}

function receivePacket(node) {
    if (node.energy > node.energyThreshold) {
        node.energy -= ENERGY_CONSUMPTION_RECEIVE;
        console.log(`节点 ${node.sNo} 接收数据，剩余能量: ${node.energy}`);
    } else {
        console.log(`节点 ${node.sNo} 能量不足，无法接收数据`);
    }
}

function tickIdle(node) {
    if (node.energy > node.energyThreshold) {
        node.energy -= ENERGY_CONSUMPTION_IDLE;
        console.log(`节点 ${node.sNo} 空闲，剩余能量: ${node.energy}`);
    } else {
        console.log(`节点 ${node.sNo} 能量不足，进入休眠状态`);
    }
}

function getDistance(node1, node2)//定义一个函数 getDistance，用于计算两个节点之间的欧几里得距离。
 {
    return Math.sqrt((node1.x - node2.x) ** 2 + (node1.y - node2.y) ** 2);
}

function calculateTransitionProbability(currentNode, nextNode, alpha, beta) {
    let pheromone = pheromoneMatrix[currentNode.sNo - 1][nextNode.sNo - 1];
    let eta = etaMatrix[currentNode.sNo - 1][nextNode.sNo - 1];
    return Math.pow(pheromone, alpha) * Math.pow(eta, beta);
}
function selectNextNode(currentNode, possibleNodes, alpha, beta) {
    let totalProbability = 0;
    let probabilities = [];

    // 使用预测位置计算距离和启发式信息
    possibleNodes.forEach(node => {
        const predictedDistance = Math.sqrt(
            (currentNode.predictedPosition[0] - node.predictedPosition[0]) ** 2 +
            (currentNode.predictedPosition[1] - node.predictedPosition[1]) ** 2
        );
        etaMatrix[currentNode.sNo - 1][node.sNo - 1] = 1 / (predictedDistance + 1e-4); // 避免除以零
    });

    // 计算转移概率
    possibleNodes.forEach(node => {
        const pheromone = pheromoneMatrix[currentNode.sNo - 1][node.sNo - 1];
        const eta = etaMatrix[currentNode.sNo - 1][node.sNo - 1];
        const probability = Math.pow(pheromone, alpha) * Math.pow(eta, beta);
        totalProbability += probability;
        probabilities.push(probability);
    });

    // 归一化概率
    probabilities = probabilities.map(p => p / totalProbability);

    // 根据概率选择下一个节点
    let random = Math.random();
    let cumulativeProbability = 0;
    for (let i = 0; i < probabilities.length; i++) {
        cumulativeProbability += probabilities[i];
        if (random < cumulativeProbability) {
            return possibleNodes[i];
        }
    }

    // 如果没有合适的节点，返回null
    return null;
}
function updatePheromone(srcNode, destNode, energyConsumed, Q, rho) {
    const srcIndex = srcNode.sNo - 1;
    const destIndex = destNode.sNo-1 ;

    if (srcIndex < 0 || srcIndex >= pub_totle_nodes || destIndex < 0 || destIndex >= pub_totle_nodes) {
        console.error(`索引超出范围：srcIndex=${srcIndex}, destIndex=${destIndex}`);
        return;
    }

    //console.log(`更新信息素：从节点 ${srcIndex + 1} 到节点 ${destIndex + 1}`);
    //console.log(`挥发前信息素浓度：${pheromoneMatrix[srcIndex][destIndex]}`);

    // 信息素挥发
    pheromoneMatrix[srcIndex][destIndex] *= (1 - rho);

    // 信息素释放
    const pheromoneDeposit = Q / energyConsumed;
    //console.log(`信息素增强量：${pheromoneDeposit}`);
    pheromoneMatrix[srcIndex][destIndex] += pheromoneDeposit;

    // 确保信息素值不超过1
    pheromoneMatrix[srcIndex][destIndex] = Math.min(1000, pheromoneMatrix[srcIndex][destIndex]);

    //console.log(`挥发后信息素浓度：${pheromoneMatrix[srcIndex][destIndex]}`);
}

function evaporatePheromone(rho)//在代码中定义 evaporatePheromone 函数，用于挥发信息素
 {
    for (let i = 0; i < pub_totle_nodes; i++) {
        for (let j = 0; j < pub_totle_nodes; j++) {
            pheromoneMatrix[i][j] *= (1 - rho);
        }
    }
}

function KalmanFilter(measurementNoise, processNoise) {
    // 初始化卡尔曼滤波的状态
    this.state = [0, 0, 0, 0]; // [x, y, vx, vy]
    this.covariance = [
        [1000, 0, 0, 0],
        [0, 1000, 0, 0],
        [0, 0, 1000, 0],
        [0, 0, 0, 1000]
    ];
    this.measurementNoise = measurementNoise; // 测量噪声
    this.processNoise = processNoise; // 过程噪声
}

KalmanFilter.prototype.predict = function() {
    // 状态转移矩阵
    const F = [
        [1, 0, 1, 0],
        [0, 1, 0, 1],
        [0, 0, 1, 0],
        [0, 0, 0, 1]
    ];
    // 过程噪声协方差矩阵
    const Q = [
        [this.processNoise, 0, 0, 0],
        [0, this.processNoise, 0, 0],
        [0, 0, this.processNoise, 0],
        [0, 0, 0, this.processNoise]
    ];
    // 预测步骤
    const newState = [
        F[0][0] * this.state[0] + F[0][1] * this.state[1] + F[0][2] * this.state[2] + F[0][3] * this.state[3],
        F[1][0] * this.state[0] + F[1][1] * this.state[1] + F[1][2] * this.state[2] + F[1][3] * this.state[3],
        F[2][0] * this.state[0] + F[2][1] * this.state[1] + F[2][2] * this.state[2] + F[2][3] * this.state[3],
        F[3][0] * this.state[0] + F[3][1] * this.state[1] + F[3][2] * this.state[2] + F[3][3] * this.state[3]
    ];
    // 更新协方差矩阵
    const newCovariance = [];
    for (let i = 0; i < 4; i++) {
        newCovariance[i] = [];
        for (let j = 0; j < 4; j++) {
            newCovariance[i][j] = 0;
            for (let k = 0; k < 4; k++) {
                newCovariance[i][j] += F[i][k] * this.covariance[k][j];
            }
        }
    }
    for (let i = 0; i < 4; i++) {
        for (let j = 0; j < 4; j++) {
            newCovariance[i][j] = F[i][j] * newCovariance[i][j];
            for (let k = 0; k < 4; k++) {
                newCovariance[i][j] += Q[i][k] * Q[k][j];
            }
        }
    }
    this.state = newState;
    this.covariance = newCovariance;
}

KalmanFilter.prototype.update = function(measurement) {
    // 测量矩阵
    const H = [
        [1, 0, 0, 0],
        [0, 1, 0, 0]
    ];
    // 测量噪声协方差矩阵
    const R = [
        [this.measurementNoise, 0],
        [0, this.measurementNoise]
    ];

    // 计算卡尔曼增益
    const S = [
        [this.covariance[0][0] + R[0][0], this.covariance[0][1] + R[0][1]],
        [this.covariance[1][0] + R[1][0], this.covariance[1][1] + R[1][1]]
    ];

    const K = [
        [this.covariance[0][0] / S[0][0], this.covariance[0][1] / S[0][1]],
        [this.covariance[1][0] / S[1][0], this.covariance[1][1] / S[1][1]],
        [this.covariance[2][0] / S[0][0], this.covariance[2][1] / S[0][1]],
        [this.covariance[3][0] / S[1][0], this.covariance[3][1] / S[1][1]]
    ];

    // 更新状态
    const innovation = [
        measurement[0] - this.state[0],
        measurement[1] - this.state[1]
    ];

    this.state[0] += K[0][0] * innovation[0] + K[0][1] * innovation[1];
    this.state[1] += K[1][0] * innovation[0] + K[1][1] * innovation[1];
    this.state[2] += K[2][0] * innovation[0] + K[2][1] * innovation[1];
    this.state[3] += K[3][0] * innovation[0] + K[3][1] * innovation[1];

    // 更新协方差矩阵
    const I = [
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1]
    ];

    const KH = [
        [K[0][0] * H[0][0] + K[0][1] * H[1][0], K[0][0] * H[0][1] + K[0][1] * H[1][1]],
        [K[1][0] * H[0][0] + K[1][1] * H[1][0], K[1][0] * H[0][1] + K[1][1] * H[1][1]],
        [K[2][0] * H[0][0] + K[2][1] * H[1][0], K[2][0] * H[0][1] + K[2][1] * H[1][1]],
        [K[3][0] * H[0][0] + K[3][1] * H[1][0], K[3][0] * H[0][1] + K[3][1] * H[1][1]]
    ];

    const newCovariance = [];
    for (let i = 0; i < 4; i++) {
        newCovariance[i] = [];
        for (let j = 0; j < 4; j++) {
            newCovariance[i][j] = I[i][j];
            for (let k = 0; k < 2; k++) {
                newCovariance[i][j] -= KH[i][k] * H[k][j];
            }
            for (let k = 0; k < 4; k++) {
                newCovariance[i][j] *= this.covariance[k][j];
            }
        }
    }

    this.covariance = newCovariance;
}
function drawSimulation() {
    // 清空画布
    clearCanvas(document.getElementById('desktop'), 0, 0, 1120, 630);

    // 绘制节点和预测路径
    Nodes.forEach(node => {
        node.drawNode('all');

        // 绘制预测路径
        if (node.predictedPosition) {
            node.ctx.beginPath();
            node.ctx.strokeStyle = 'rgba(255, 0, 0, 0.5)';
            node.ctx.moveTo(node.x, node.y);
            node.ctx.lineTo(node.predictedPosition[0], node.predictedPosition[1]);
            node.ctx.stroke();
        }
    });

    // 绘制优化后的路由选择结果
    // ... 路由绘制代码
}

function sendCtrlMsg(){
}

function sendDataMsg(){
}

function recvMsg(){
}

function findNeighbor(){
}

function moveNodes(){
   
}


//---------------------------------------------
exports = onLoad;

exports = panelDisp;
exports = getLocalData;
exports = setLocalData;
exports = storeParam;