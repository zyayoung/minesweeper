#include <iostream>
#include <ctime>
#include <cstdlib>
#include <string.h>
#include <unistd.h>
int MineCount=99;
#define RowMAX 30
#define ColMAX 16
int Row = 30;
int Col = 16;
int skipped=0;
int trydpth=64;//暴力递归阀值 越低越快 0表示关闭爆力
int cnt=1000;
#define Qlength RowMAX*ColMAX*2
#define ShowProcess 1 //0 sweeps faster

using namespace std;
const int speed=1;
int cellState[RowMAX+2][ColMAX+2];//0- + 1-雷 2-以扫
int cellMineNextTo[RowMAX+2][ColMAX+2];//d存储每个格子周围的雷数
int toFind = Row*Col;
int losecnt,wincnt;
int gameflag=0,Detected=0; //0=ing 1=fail 2=success

void showConclusion(){
    //if((wincnt+losecnt)%1000==0)
        cout<<wincnt<<"/"<<wincnt+losecnt<<"="<<(float)(wincnt*100)/(float)(wincnt+losecnt)<<"%"<<endl;
//	cout<<(float)(wincnt*100)/(float)(wincnt+losecnt)<<"% "<<skipped<<endl;
}

void DisplayCurrentState(){
    
    for(int i=1;i<=50000;i++)
		sleep(0.5);
	system("clear");
    //cout<<endl;
    cout<<"Current success rate="<<wincnt<<"/"<<wincnt+losecnt<<"="<<(float)(wincnt*100)/(float)(wincnt+losecnt)<<"%"<<endl;
    //if(gameflag==0)
    cout<<"Process: "<<Col*Row-toFind+Detected<<"/"<<Col*Row<<"="<<(int)((float)(Col*Row-toFind+Detected)*100/(float)(Col*Row))<<"%"<<"\t  Findded: "<<Detected<<"/"<<MineCount<<"="<<(int)((float)(Detected*100)/(float)(MineCount))<<"%"<<endl;
    //if(gameflag==2)cout<<"Congratulation"<<endl;
    
    //cout<<"---------------------------------------------"<<endl;
    cout<<endl;
    for(int i=Col;i>=1;i--){
        for(int j=1;j<=Row;j++){
            if(cellState[j][i]==0)cout<<"#";
            else if(cellState[j][i]==1)cout<<"@";
            else if(cellState[j][i]==2){
                if(cellMineNextTo[j][i]==0)cout<<'.';
                else cout<<cellMineNextTo[j][i];
            }
            else if(cellState[j][i]==3){
                cout<<"X";
            }
            cout<<' ';
        }
        cout<<endl;
    }
//    for(int j=1;j<=Row;j++)cout<<' ';
    //cout<<"\n";
    //for(int i=1;i<=200;i++)sleep(0.1);
    
}


int qused=1,qx[Qlength],qy[Qlength],qnxt[Qlength];//链表，用于记录活跃的带数字的格子（每局清空一次）
//模拟点按
void point(int x,int y,int ori=1){
    if(cellMineNextTo[x][y]==-1){
		DisplayCurrentState();
		sleep(2);
        cout<<"--------------perror"<<endl;
        //while(1);
    }
    if(cellState[x][y])return;
    cellState[x][y]=2;
    toFind--;
    if(cellMineNextTo[x][y]>0){
        qx[qused]=x,qy[qused]=y;
        qnxt[qused]=qnxt[0],qnxt[0]=qused;
        qused++;
    }
    if(cellMineNextTo[x][y]==0)
    for(int j=x-1;j<=x+1;j++)
        for(int k=y-1;k<=y+1;k++)
            if(j>0&&j<=Row&&k>0&&k<=Col)point(j,k,0);
#if ShowProcess
    if (ori==1) {
        DisplayCurrentState();
    }
#endif
}
//标记雷
void tagmine(int x,int y){
    if(cellState[x][y])return;
    if(cellState[x][y]==0&&x>=1&&x<=Row&&y>=1&&y<=Col){
        Detected++;
        if(cellMineNextTo[x][y]!=-1){
            cout<<"--------------terror"<<endl;
            //while(1);
        }
        cellState[x][y]=1;
#if ShowProcess
        //cout<<'t'<<x<<y<<endl;
        DisplayCurrentState();
#endif
    }

}
//生成地图
void gen(int px, int py){
    for(int j=0;j<=Row+1;j++)
    for(int k=0;k<=Col+1;k++)
    cellMineNextTo[j][k]=0,cellState[j][k]=0;
    
    Detected=0;
    qused=1;
    qnxt[0]=0;
    toFind=Row*Col;
    
    int x=rand()%Row+1,y=rand()%Col+1;
    for(int i=0;i<MineCount;i++){
        while(cellMineNextTo[x][y]==-1||(abs(x-px)<=1&&abs(y-py)<=1)) x=rand()%Row+1,y=rand()%Col+1;
        cellMineNextTo[x][y]=-1;
        for(int j=x-1;j<=x+1;j++)
        for(int k=y-1;k<=y+1;k++)
        if(j>0&&j<=Row&&k>0&&k<=Col&&cellMineNextTo[j][k]!=-1)cellMineNextTo[j][k]++;
    }
}

/*-----------------------------------
|                                     |
|   以下是扫雷函数 按顺序使用：            |
|   单个数字简单逻辑推理                  |
|   多个数字简单逻辑推理                  |
|   ForceAnalyse - 暴力搜索雷／非雷方块   |
|   按概率点选未扫方块                   |
|                                     |
-----------------------------------*/

//多个数字简单逻辑推理 数据部分
int setx[Qlength*10][8],sety[Qlength*10][8],setused[Qlength*10],setmine[Qlength*10],sused=0;//集合
int seth[RowMAX+2][ColMAX+2],shused=1;//判断子集用的hash表

//暴力搜索 数据部分
int tmpqx[Qlength],tmpqy[Qlength],tmpqused=0;//记录雷可能出现在的位置
int caseh[RowMAX+2][ColMAX+2],visited[RowMAX+2][ColMAX+2],casecnt=0,minecnt;//记录所有可能情况的hash表
int p[RowMAX+2][ColMAX+2];

void ForceAnalyse(int from, int toadd){
    if(from<tmpqused){
		int x=tmpqx[from],y=tmpqy[from],flaga=1,counta=1,flagb=1,countb=0;
		visited[x][y]=1;
		for(int m=x-1;m<=x+1;m++){
			for(int n=y-1;n<=y+1;n++){
				//if (m>=1&&m<=Row&&n>=1&&n<=Col&&cellState[m][n]==2&&cellMineNextTo[m][n]>0) {
				if(seth[m][n]==shused){
					//cout<<m<<"\t"<<n<<"\t"<<seth[m][n]<<"\t"<<shused<<endl;
					counta=1;
					countb=0;
					for(int j=m-1;j<=m+1;j++){
						for(int k=n-1;k<=n+1;k++){
							if(cellState[j][k]==1){
								counta++;
							}
							if(((cellState[j][k]==0&&!visited[j][k])||cellState[j][k]==1)&&j>0&&j<=Row&&k>0&&k<=Col){
								countb++;
							}
						}
					}
					if (counta>cellMineNextTo[m][n]) {
						flaga=0;
					}
					if (countb<cellMineNextTo[m][n]) {
						flagb=0;
						if(!flaga){
							visited[x][y]=0;
							return;
						}
					}
				}
			}
		}
		//cout<<flagb;
		if(flagb)
			ForceAnalyse(from+1, toadd);
        if(toadd>0&&flaga){
            //int x=tmpqx[from],y=tmpqy[from],count=0;
            //cellState[x][y]=1;
            
            cellState[x][y]=1;
            ForceAnalyse(from+1, toadd-1);
            cellState[x][y]=0;
        }
        visited[x][y]=0;
    }
    else if(from==tmpqused){
        casecnt++;
        for(int i=0;i<tmpqused;i++){
            //cout<<"-"<<tmpqx[i]<<tmpqy[i]<<endl;
            if(cellState[tmpqx[i]][tmpqy[i]]==1){
                caseh[tmpqx[i]][tmpqy[i]]++;
                //minecnt++;
			}
        }
        //cout<<"Case:"<<casecnt<<endl;
        //DisplayCurrentState();
    }
    return ;
}

void  addlinked(int x, int y){
	seth[x][y]=0;
	tmpqx[tmpqused]=x,tmpqy[tmpqused]=y,tmpqused++;
	for(int j=x-2;j<=x+2;j++){
		for(int k=y-2;k<=y+2;k++){
			if(j>0&&j<=Row&&k>0&&k<=Col&&seth[j][k]==shused){
				addlinked(j,k);
			}
		}
	}
}

int MineSweeper(){//tag是扫雷机状态 0表示没有进展 1表示发现雷／非雷方块
    int x,y,empty=0,dtcnt=0,qpre=0,tag=0;
    if(MineCount==Detected){
        for(int j=1;j<=Row;j++)
        for(int k=1;k<=Col;k++)
        if(cellState[j][k]==0)point(j,k);
        return 0;
    }
    for(int qtmp=qnxt[0];qtmp!=0;qtmp=qnxt[qtmp]){
        x=qx[qtmp],y=qy[qtmp];
        //cout<<x<<' '<<y<<' '<<qpre<<' '<<qtmp;
        empty=0,dtcnt=0;
        for(int j=x-1;j<=x+1;j++){
            for(int k=y-1;k<=y+1;k++){
                if(j>0&&j<=Row&&k>0&&k<=Col){
                    if(cellState[j][k]==1)dtcnt++;
                    else if(cellState[j][k]==0)empty++;
                }
            }
        }
        //cout<<" "<<
        if(dtcnt==cellMineNextTo[x][y]){
            //cout<<" p";
            qnxt[qpre]=qnxt[qtmp];
            qtmp=qpre;
            tag=1;
            for(int j=x-1;j<=x+1;j++)
                for(int k=y-1;k<=y+1;k++)
                    if(cellState[j][k]==0&&j>0&&j<=Row&&k>0&&k<=Col)point(j,k);
        }
        else if(empty==cellMineNextTo[x][y]-dtcnt){
            //cout<<" t";
            qnxt[qpre]=qnxt[qtmp];
            qtmp=qpre;
            tag=1;
            for(int j=x-1;j<=x+1;j++)
                for(int k=y-1;k<=y+1;k++)
                    tagmine(j, k);
        }
        qpre=qtmp;
        //cout<<endl;
    }
    //for(int qtmp=qnxt[0];qtmp!=0;qtmp=qnxt[qtmp])
    //cout<<qx[qtmp]<<' '<<qy[qtmp]<<' '<<qtmp<<endl;
    if(tag==0){
        //DisplayCurrentState();
        sused=0;
        setused[0]=0;
        int sthfound=0;
        for(int qtmp=qnxt[0];qtmp!=0;qtmp=qnxt[qtmp]){
            x=qx[qtmp],y=qy[qtmp];
            dtcnt=0;
            for(int j=x-1;j<=x+1;j++){
                for(int k=y-1;k<=y+1;k++){
                    if(cellState[j][k]==0&&j>0&&j<=Row&&k>0&&k<=Col){
                        sthfound=1;
                        setx[sused][setused[sused]]=j;
                        sety[sused][setused[sused]]=k;
                        setused[sused]++;
                        //cout<<"-->added "<<j<<k<<"to set "<<sused<<endl;
                    }
                    if(cellState[j][k]==1)dtcnt++;
                }
            }
            if(sthfound){
                setmine[sused]=cellMineNextTo[x][y]-dtcnt;
                
                sused++;
                setused[sused]=0;
            }
        }
//        int presused=sused;
        for(int i=0;i<sused;i++){
            for(int j=0;j<sused;j++){
                if (i==j||setused[i]<setused[j]) {
                    continue;
                }
                shused++;
                if(shused>2100000000){
                    shused=1;
                    for(int j=1;j<=Row;j++){
                        for(int k=1;k<=Col;k++){
                            seth[j][k]=0;
                        }
                    }
                }
                for(int k=0;k<setused[i];k++){
                    seth[setx[i][k]][sety[i][k]]=shused;
                }
                int flag=1;
                for(int k=0;k<setused[j];k++){
                    if(seth[setx[j][k]][sety[j][k]]!=shused){
                        flag=0;
                        break;
                    }
                    seth[setx[j][k]][sety[j][k]]=0;
                }
                if(flag){
                    //cout<<"findsubset"<<endl;
                    flag=0;
                    for(int k=0;k<setused[i];k++){
                        if(seth[setx[i][k]][sety[i][k]]==shused){
                            flag=1;
                            setx[sused][setused[sused]]=setx[i][k];
                            sety[sused][setused[sused]]=sety[i][k];
                            //cout<<"--->added "<<setx[i][k]<<sety[i][k]<<"to subset "<<sused<<"-"<<setused[sused]<<endl;
                            setused[sused]++;
                        }
                    }
                    if(flag){
                        int existed=0;
                        for(int tmp=sused-1;tmp>=0;tmp--){
                            if(setused[sused]==setused[tmp]){
                                existed=1;
                                for(int k=0;k<setused[tmp];k++){
                                    if(setx[tmp][k]!=setx[sused][k]||sety[tmp][k]!=sety[sused][k]){
                                        existed=0;
                                        break;
                                    }
                                }
                            }
                            if(existed)break;
                        }
                        if(existed){
                            setused[sused]=0;
                        }
                        else{
                            setmine[sused]=setmine[i]-setmine[j];
                            //setfa[sused]=i;
                            //cout<<"set "<<i<<" includes set"<<j<<endl;
                            sused++;
                            setused[sused]=0;
                        }
                    }
                }
            }
        }
        //cout<<" presused:"<<presused<<" sused:"<<sused<<endl;
        for(int i=0;i<sused;i++){
            //empty=0,dtcnt=0;
            //for(int k=0;k<setused[i];k++)
            if(setmine[i]==0){
//                cout<<"logicp"<<endl;
                for(int k=0;k<setused[i];k++){
                    //cout<<"logicp"<<setx[i][k]<<sety[i][k]<<endl;
                    point(setx[i][k], sety[i][k]);
                    tag=1;
                }
            }
            else if(setmine[i]==setused[i]){
                for(int k=0;k<setused[i];k++){
                    //cout<<"logict"<<setx[i][k]<<sety[i][k]<<endl;
                    tagmine(setx[i][k],sety[i][k]);
                    tag=1;
                }
            }
        }
    }
    
    if(tag==0&&trydpth>0){
        //sumcasecnt=0;
        minecnt=0;
        shused++;
        tmpqused=0;
        if(shused>2100000000){
            shused=2;
            for(int j=1;j<=Row;j++){
                for(int k=1;k<=Col;k++){
                    seth[j][k]=0;
                }
            }
        }
        for(int j=1;j<=Row;j++){
			for(int k=1;k<=Col;k++){
				caseh[j][k]=0;
			}
		}
        for(int qtmp=qnxt[0];qtmp!=0;qtmp=qnxt[qtmp]){
            x=qx[qtmp],y=qy[qtmp];
            seth[x][y]=shused+1;
            //cout<<"find"<<x<<y<<endl;
            for(int j=x-1;j<=x+1;j++){
                for(int k=y-1;k<=y+1;k++){
                    if(cellState[j][k]==0&&j>0&&j<=Row&&k>0&&k<=Col){
                        if(seth[j][k]!=shused){
                            tmpqx[tmpqused]=j,tmpqy[tmpqused]=k,tmpqused++;
                            seth[j][k]=shused;
                        }
                    }
                }
            }
        }
        //shused++;
        //int flagabc=0;
        for(int j=1;j<=Row;j++){
			for(int k=1;k<=Col;k++){
				if(seth[j][k]==shused){
					tmpqused=0;
					//if(flagabc)cout<<"time saved"<<endl;
					//flagabc=1;
					addlinked(j,k);
					if(tmpqused>=trydpth){
						//cout<<tmpqused<<" skip";
						skipped++;
					}
					else{
						casecnt=0;
						//minecnt=0;
						//cout<<"c"<<tmpqused<<endl;
						shused++;
						/*for(int j=1;j<=Row;j++){
							for(int k=1;k<=Col;k++){
								caseh[j][k]=0;
							}
						}*/
						ForceAnalyse(0,MineCount-Detected);
						shused--;
						//if (casecnt==0)cout<<"WTF"<<endl;
						//if (casecnt!=0) {
						for(int i=0;i<tmpqused;i++){
							//p[tmpqx[i]][tmpqy[i]]=casecnt;
							if(caseh[tmpqx[i]][tmpqy[i]]==casecnt){
								//cout<<" t"<<tmpqx[i]<<tmpqy[i];
								tagmine(tmpqx[i], tmpqy[i]),tag=1;
							}
							else if(caseh[tmpqx[i]][tmpqy[i]]==0){
								//cout<<" p"<<tmpqx[i]<<" "<<tmpqy[i];
								point(tmpqx[i], tmpqy[i]),tag=1;
							}
							//minecnt+=caseh[tmpqx[i]][tmpqy[i]]*10000/casecnt;
							else{
								caseh[tmpqx[i]][tmpqy[i]]=caseh[tmpqx[i]][tmpqy[i]]*10000/casecnt;
								minecnt+=caseh[tmpqx[i]][tmpqy[i]];
							}
								//caseh[tmpqx[i]][tmpqy[i]]=0;
							//}
						}
					}
				}
			}
		}
        //cout<<"c"<<tmpqused;
        shused++;
        //cout<<endl;
    }
    if(tag==0&&toFind>MineCount){
        //cout<<"Fail"<<toFind<<" "<<MineCount<<endl;
        //DisplayCurrentState();
        int sum=0,min=2100000000,px=2,py=2;
        for(int x=Row;x>0;x--){
            for(int y=Col;y>0;y--){
                if(cellState[x][y]!=0)continue;
                if(casecnt>1){
                    //cout<<"p";
                    if(caseh[x][y]){
                        sum=caseh[x][y];
                        //cout<<sum<<endl;
                    }
                    else{
                        sum=((MineCount-Detected)*10000-minecnt)/(toFind-Detected-minecnt/10000);
                        //cout<<sum<<endl;
                    }
                }
                else{
                    //cout<<"p";
                    sum=0;
                    for(int j=x-1;j<=x+1;j++){
                        for(int k=y-1;k<=y+1;k++){
                            if(cellState[j][k]==2&&j>0&&j<=Row&&k>0&&k<=Col){
                                sum+=cellMineNextTo[j][k]*2;
                            }
                            if(cellState[j][k]==1)sum-=1;
                        }
                    }
                }
                if(sum==0){
                    px=x;
                    py=y;
                    break;
                }
                if(sum<min){
                    min=sum;
                    px=x;
                    py=y;
                }
                else if(sum==min){
                    if(abs(x-Row/2-1)+abs(y-Col/2-1)>abs(px-Row/2-1)+abs(py-Col/2-1)){
					//if(abs(x-Row/2-1)<abs(px-Row/2-1)){
                        px=x;
                        py=y;
                    }
                }
            }
        }
        //cout<<min<<endl;
        //cout<<"p"<<x<<y<<endl;
        if (cellMineNextTo[px][py]==-1) {
            cellState[px][py]=3;
            //cout<<"!"<<endl;
            return 0;
        }
        point(px, py);
        tag=1;
    }
    
    return tag;
}


string inpt;
int main(int argc,char **argv){
    ios::sync_with_stdio(false);
    //cout<<argc;
    unsigned long long seed=time(NULL);
    for (int i=0; i<argc; i++) {
        //cout<<argv[i]<<endl;
        if (!strcmp(argv[i],"-trydpth")) {
            trydpth = atoi(argv[i+1]);
        }
        if (!strcmp(argv[i],"-cnt")) {
            cnt = atoi(argv[i+1]);
        }
        if (!strcmp(argv[i],"-minecount")) {
            MineCount = atoi(argv[i+1]);
        }
        if (!strcmp(argv[i],"-row")) {
            Row = atoi(argv[i+1]);
        }
        if (!strcmp(argv[i],"-col")) {
            Col = atoi(argv[i+1]);
        }
        if (!strcmp(argv[i],"-seed")) {
            seed = atoi(argv[i+1]);
        }
    
    }
    srand(seed);
    int px,py;
    //time_t start,stop;
    //start = time(NULL);
    //for(int i=1;i<=40;i++){
		//cout<<""<<i<<" ";
		//trydpth=i;
		//start = time(NULL);
		wincnt=0;
		losecnt=0;
		skipped=0;
        //cout<<" "<<trydpth<<endl;
		while(wincnt+losecnt<cnt){
			px=Row/2+1,py=Col/2+1;
			gen(px,py);
	#if ShowProcess
			sleep(speed);
			DisplayCurrentState();
			sleep(speed);
	#endif
			point(px,py);
			//gameflag = 0;
			while(MineSweeper());
			//DisplayCurrentState();
			if(toFind==MineCount){
				//gameflag=2;
				wincnt++;
			}
			else {
				losecnt++;
				//DisplayCurrentState();
				//sleep(5);
			}
			//if((wincnt+losecnt)%outf==0)showConclusion();
			
	#if ShowProcess
			DisplayCurrentState();
			sleep(speed);
	#endif
			showConclusion();
		}
		//stop = time(NULL);
		//printf("%ld ",(stop-start));
		
		//cout<<(stop-start)<<" ";
		showConclusion();
	//}
}
